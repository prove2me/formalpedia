-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_on_built
-- name    : Formalism.L2.Indef.Tree.on_built
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:35:37.825009+00:00
-- url     : https://prove2.me/theorems/db26252b-43dc-50fc-bfbd-5bf7211ea3fc
-- title:
--   Tree: on built
-- statement:
--   The Tree construction uses the on built property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L894-L904
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L894-L904

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

theorem Formalism.L2.Indef.Tree.on_built (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) :
    ({ S with err0 := O.errOn } : IndefData Df).ON N := by sorry
