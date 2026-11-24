-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_integral_scale_two
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.integral_scale_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:43.002304+00:00
-- url     : https://prove2.me/theorems/87b50c5b-0eb2-46d6-9e05-d098df64c137
-- title:
--   Two Variable Swap Lemmas: integral scale two
-- statement:
--   The Two Variable Swap Lemmas construction uses the integral scale two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L253-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L253-L257

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

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.integral_scale_two {u v : K} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (i : Fin 2) :
    Integral (sc2 u v i) := by sorry
