-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_single_variable
-- name    : Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_single_variable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:16.950912+00:00
-- url     : https://prove2.me/theorems/5f39606d-c16b-4e6f-814f-7679880db026
-- title:
--   Gram Frame Composition Lin Facts: subst single variable
-- statement:
--   The Gram Frame Composition Lin Facts construction uses the subst single variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L104-L107

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_single_variable {τ κ : Type} {b : τ → MvPowerSeries κ K} (hb : HasSubst b) (x : τ)
    (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by sorry
