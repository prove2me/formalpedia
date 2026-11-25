-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_on_family
-- name    : Formalism.L2.Indef.Tree.on_family
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:36:42.1718+00:00
-- url     : https://prove2.me/theorems/c42d3444-0f47-5a52-b49d-e998c1f52512
-- title:
--   Tree: on family
-- statement:
--   The Tree construction uses the on family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L952-L964
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L952-L964

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

theorem Formalism.L2.Indef.Tree.on_family (c : OnConst) : ∃ CE : ℝ, CE = c.CE ∧
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [StarRing K₁] (Bs : DefBase K₁) (Df : DefSide Bs) (R : IndefRows Df),
      Df.WF → ∀ (N : IndefNum Bs) (P : Type) [Group P] [Finite P] (O : OnObj R.toIndefData P c),
      LeafMackey O → LeafSup O → LeafProj O → TieCoord O → LeafSpan O → LeafLemmaS O → LatticeIndexBoundAtPairs O → LeafData O →
      LeafRankJ O → LeafIdentity O → LeafTW2 O → LeafTW1 O → LeafShareI O → LeafIndexU O → LeafBadShare O →
      LeafUnip O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O →
      LeafSizes O → LeafX O → LeafBad O → LeafJSum O → LeafJExp N O → ErrorConstantMatchesDefinition N O CE → TieErr O →
      R.toIndefData.ON N := by sorry
