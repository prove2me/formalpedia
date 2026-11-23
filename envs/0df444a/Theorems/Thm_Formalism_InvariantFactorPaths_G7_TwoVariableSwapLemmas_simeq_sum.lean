-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_sum
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.simeq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:19.691028+00:00
-- url     : https://prove2.me/theorems/fa0f4e36-0a8f-4883-8727-173abc5c757c
-- title:
--   Two Variable Swap Lemmas: simeq sum
-- statement:
--   The Two Variable Swap Lemmas construction uses the simeq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L233-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L233-L242

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.simeq_sum (hS : SimeqRules) {ι : Type} (s : Finset ℕ) (f : ℕ → MvPowerSeries ι K)
    (h : ∀ k ∈ s, Simeq (f k) 0) : Simeq (∑ k ∈ s, f k) 0 := by sorry
