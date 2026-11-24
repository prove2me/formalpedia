-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_integral_scale_three
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.integral_scale_three
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:07.875682+00:00
-- url     : https://prove2.me/theorems/c4b107c8-d803-4b96-86f5-dfed90cae463
-- title:
--   Two Variable Swap Lemmas: integral scale three
-- statement:
--   The Two Variable Swap Lemmas construction uses the integral scale three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L259-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L259-L264

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

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.integral_scale_three {u v : K} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (i : Fin 3) :
    Integral (sc3 u v i) := by sorry
