-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_single_log_derivative
-- name    : Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.integral_single_log_derivative
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:03.705483+00:00
-- url     : https://prove2.me/theorems/26e20138-68c7-418a-b170-dc9a825cb49b
-- title:
--   Gram Frame Composition Lin Facts: integral single log derivative
-- statement:
--   The Gram Frame Composition Lin Facts construction uses the integral single log derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L244-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L244-L251

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

theorem Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.integral_single_log_derivative {τ : Type} {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (x : τ) :
    Integral (at1 x (PowerSeries.derivative K (lgF K p))) := by sorry
