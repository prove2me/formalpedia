-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_example_negative_content_fails
-- name    : Formalism.L2.Indef.Tree.example_negative_content_fails
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:21.687631+00:00
-- url     : https://prove2.me/theorems/60c6ba02-d21d-503d-b5c0-d18caf5c39fc
-- title:
--   Tree: example negative content fails
-- statement:
--   The Tree construction uses the example negative content fails property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L1543-L1575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L1543-L1575

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
variable (K)
variable {K} (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))
variable (h3 : ∀ w ∈ Tw0, plc w = 3)
include h3
omit h3

theorem Formalism.L2.Indef.Tree.example_negative_content_fails (w0 : HeightOneSpectrum (𝓞 K)) (h3w : plc w0 = 3) (E : ℝ) :
    ¬ LeafDepthGood (exampleConstants K v0 (-10) E) (exampleObject K v0 {w0}) ∧
    ¬ ({ exampleIndefiniteData K v0 {w0} 0 with err0 := (exampleObject K v0 {w0}).errOn } : IndefData (exampleDf K v0)).ON (exampleConstants K v0 (-10) E) := by sorry
