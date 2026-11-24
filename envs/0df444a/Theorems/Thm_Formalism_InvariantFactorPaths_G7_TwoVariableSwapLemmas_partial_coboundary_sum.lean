-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_partial_coboundary_sum
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:26.480316+00:00
-- url     : https://prove2.me/theorems/6d53d526-d82a-4a9c-a017-80f7ec580825
-- title:
--   Two Variable Swap Lemmas: partial coboundary sum
-- statement:
--   The Two Variable Swap Lemmas construction uses the partial coboundary sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L214-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L214-L221

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
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
open Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
open MvPowerSeries
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_sum {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (s : Finset ℕ)
    (f : ℕ → MvPowerSeries (Fin 2) K) : d1 F (∑ k ∈ s, f k) = ∑ k ∈ s, d1 F (f k) := by sorry
