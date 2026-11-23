-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_lin
-- name    : Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.integral_lin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:49.457909+00:00
-- url     : https://prove2.me/theorems/b2540ec7-a0ac-439d-8f41-61a9d69c5f46
-- title:
--   Gram Frame Composition Lin Facts: integral lin
-- statement:
--   The Gram Frame Composition Lin Facts construction uses the integral lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L208-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L208-L220

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.integral_lin [CharZero K] {τ κ : Type} [Finite τ] {D : MvPowerSeries τ K}
    (hD0 : constantCoeff D = 0) (hDi : Integral (mvExp D)) {b : τ → MvPowerSeries κ K}
    (hb0 : ∀ i, constantCoeff (b i) = 0) (hbi : ∀ i, Integral (b i)) (hbD : subst b D = 0)
    (e : τ) : Integral (subst b (pderiv K e D)) := by sorry
