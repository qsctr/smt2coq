{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Main where

import           Data.Foldable
import           Data.List.NonEmpty            (NonEmpty)
import qualified Data.List.NonEmpty            as NE
import           Data.Map.Strict               (Map)
import qualified Data.Map.Strict               as Map
import           Data.Maybe
import           Data.Sequence                 (Seq, (|>))
import qualified Data.Sequence                 as Seq
import qualified Data.Text                     as Text
import qualified Data.Text.IO                  as Text
import qualified Data.Text.Read                as Text.Read
import           Language.Coq.Gallina          as Coq
import           Language.Coq.Pretty
import           Language.Coq.Util.PrettyPrint
import           Language.SMT2.Parser          (parseFileMsg, script)
import           Language.SMT2.Syntax          as SMT2
import           System.Environment
import           System.FilePath
import           System.IO

main :: IO ()
main = do
    filenames <- getArgs
    for_ filenames $ \filename -> do
        smt2 <- Text.readFile filename
        case parseFileMsg script smt2 of
            Left err -> Text.putStrLn $ "Parse error: " <> err
            Right cmds -> do
                let baseName = fromMaybe filename $
                        stripExtension "smt2" filename
                    coqBaseName = map tr baseName
                      where tr '-' = '_'
                            tr x   = x
                withFile (coqBaseName ++ ".v") WriteMode $ \h ->
                    for_ (translate cmds) $ \sentence -> do
                        displayIO h $ renderPretty 1 160 $
                            renderGallina sentence
                        hPutStr h "\n\n"

type FunctionDecls = Map Ident (Binders, Coq.Term, NonEmpty MatchItem)

data Env = Env
    { datatypes     :: Seq Inductive
    , functions     :: Seq Ident
    , functionDecls :: FunctionDecls
    , functionEqns  :: Map Ident (Seq Equation)
    , definitions   :: Seq Definition
    , theorems      :: Seq Coq.Term }
  deriving Show

initEnv :: Env
initEnv = Env [] [] [] [] [] []

translate :: Script -> [Sentence]
translate = envToSentences . foldl' trans initEnv

envToSentences :: Env -> [Sentence]
envToSentences Env {..} = ModuleSentence (Require Nothing (Just Import) imports)
    : map InductiveSentence (toList datatypes)
    ++ mapMaybe buildFunc (toList functions)
    -- ++ map DefinitionSentence (toList definitions)
    ++ toList (Seq.mapWithIndex buildThm theorems)
  where buildFunc fnName
            | null eqns = Nothing
            | otherwise = Just $ FixpointSentence $ Fixpoint
                [FixBody (Bare $ trName fnName)
                    binders Nothing (Just retType) body]
                []
          where eqns = functionEqns Map.! fnName
                (binders, retType, matchItems) = functionDecls Map.! fnName
                body = Match matchItems Nothing $ toList eqns
        buildThm i thm = AssertionSentence
            (Assertion Theorem (Bare $ "theorem" <> Text.pack (show i)) [] thm)
            (ProofAdmitted "")

imports :: NonEmpty ModuleIdent
imports = ["Nat", "Arith"]

trans :: Env -> Command -> Env
trans Env {..} cmd = case cmd of
    DeclareDatatypes sortDecs ddDecs ->
        let ind = Inductive (NE.zipWith mkIndBody sortDecs ddDecs) []
            mkIndBody (SortDec sort _) (DDNonparametric ctors) =
                IndBody (Bare $ trName sort) [] (qb "Type") $
                    map trCtor $ toList ctors
              where trCtor (ConstructorDec ctorName sels) =
                        (Bare $ trName ctorName, [], Just $
                            foldr (Arrow . getType) (qb $ trName sort) sels)
                    getType (SelectorDec _ s) = sortToType s
            mkIndBody _ ddDec =
                error $ "Could not translate datatype definition " ++ show ddDec
        in  Env { datatypes = datatypes |> ind, .. }
    DeclareFun fName argSorts retSort ->
        let (binders, matchItems) = NE.unzip $ NE.fromList $
                zipWith mkBinderMatch argSorts [0 :: Int ..]
            mkBinderMatch argSort i = (binder, matchItem)
              where binder = Typed Ungeneralizable Explicit [Ident qualid] $
                        sortToType argSort
                    matchItem = MatchItem (Qualid qualid) Nothing Nothing
                    qualid = Bare $ trName fName <> "_arg" <> Text.pack (show i)
        in  Env { functions = functions |> fName
                , functionDecls = Map.insert fName
                    (binders, sortToType retSort, matchItems) functionDecls
                , functionEqns = Map.insert fName [] functionEqns
                , .. }
    DefineFun (FunctionDef fName args retSort body) ->
        let def = DefinitionDef Global (Bare $ trName fName)
                (map sortedVarToBinder args) (Just $ sortToType retSort) $
                    trTerm body
        in  Env { definitions = definitions |> def, .. }
    Assert term ->
        let tryAddFunEqn
                (TermApplication (Unqualified (IdSymbol "="))
                    [TermApplication (Unqualified (IdSymbol f)) args, body])
                | Map.member f functionEqns = addFunEqn f args $ trTerm body
            tryAddFunEqn (TermApplication (Unqualified (IdSymbol f)) args)
                | returnsBool f functionDecls = addFunEqn f args $ qb "true"
            tryAddFunEqn (TermForall _ term') = tryAddFunEqn term'
            tryAddFunEqn _ = Nothing
            addFunEqn f args body = Just $
                Env { functionEqns = Map.adjust (|> eqn) f functionEqns, .. }
              where eqn = Equation [MultPattern $ NE.map argToPat args] body
                    argToPat (TermQualIdentifier (Unqualified (IdSymbol x))) =
                        QualidPat $ Bare $ trName x
                    argToPat
                        (TermApplication (Unqualified (IdSymbol c)) cArgs) =
                            ArgsPat (Bare $ trName c) $
                                map argToPat $ toList cArgs
                    argToPat arg = error $
                        "Could not translate to pattern: " ++ show arg
            addThm term' = Env
                { theorems = theorems |> termToThm functionDecls term', ..}
        in  case tryAddFunEqn term of
                Just env -> env
                Nothing -> case term of
                    TermApplication (Unqualified (IdSymbol "not")) [term'] ->
                        addThm term'
                    _ -> addThm term
    CheckSat -> Env {..}
    _ -> error $ "Could not translate command: " ++ show cmd

sortToType :: SMT2.Sort -> Coq.Term
sortToType (SortSymbol (IdSymbol s)) = qb $ case s of
    "Int"  -> "nat"
    "Bool" -> "bool"
    _      ->  trName s
sortToType sort = error $ "Could not translate sort: " ++ show sort

trTerm :: SMT2.Term -> Coq.Term
trTerm (TermSpecConstant (SCNumeral n)) = case Text.Read.decimal n of
    Right (num, "") -> Num num
    _               -> error $ Text.unpack $ "Could not parse number " <> n
trTerm (TermQualIdentifier (Unqualified (IdSymbol s))) = qb $ trName s
trTerm (TermApplication (Unqualified (IdSymbol f)) args)
    | f == "ite", [i, t, e] <- args =
        If SymmetricIf (trTerm i) Nothing (trTerm t) (trTerm e)
    | f `elem` shouldFold =
        foldr1 (\x y -> App tf [PosArg x, PosArg y]) $ NE.map trTerm args
    | otherwise = App tf $ NE.map (PosArg . trTerm) args
  where tf = qb $ case f of
            "="   -> "eqb"
            "+"   -> "plus"
            "-"   -> "minus"
            "<"   -> "ltb"
            "<="  -> "leb"
            "and" -> "andb"
            "or"  -> "orb"
            "not" -> "negb"
            _     -> trName f
        shouldFold = ["and", "or"] :: [Symbol]
trTerm term = error $ "Could not translate term: " ++ show term

termToThm :: FunctionDecls -> SMT2.Term -> Coq.Term
termToThm functionDecls = tr
  where tr (TermForall vars term) =
            Forall (NE.map sortedVarToBinder vars) $ tr term
        tr term@(TermApplication (Unqualified (IdSymbol f)) args)
            | f == "=>", [t1, t2] <- args = Arrow (tr t1) (tr t2)
            | Just rel <- getRel = App (qb rel) $ NE.map (PosArg . trTerm) args
            | returnsBool f functionDecls =
                App (qb "eq") [PosArg $ trTerm term, PosArg $ qb "true"]
            | otherwise = App (qb $ trName f) $ NE.map (PosArg . tr) args
          where getRel = case f of
                    "="  -> Just "eq"
                    ">=" -> Just "ge"
                    _    -> Nothing
        tr term = trTerm term

sortedVarToBinder :: SortedVar -> Binder
sortedVarToBinder (SortedVar sym sort) =
    Typed Ungeneralizable Explicit [Ident $ Bare sym] $ sortToType sort

returnsBool :: Ident -> FunctionDecls -> Bool
returnsBool f functionDecls = case Map.lookup f functionDecls of
    Just (_, Qualid (Bare "bool"), _) -> True
    _                                 -> False

trName :: Symbol -> Ident
trName = Text.replace "-" "_"

qb :: Ident -> Coq.Term
qb = Qualid . Bare
