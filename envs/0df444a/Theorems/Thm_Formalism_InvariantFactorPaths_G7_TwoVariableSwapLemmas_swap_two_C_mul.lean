-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_C_mul
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.swap_two_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:32.355245+00:00
-- url     : https://prove2.me/theorems/aa7edd44-a0a9-40b0-804b-6bf6c8e19072
-- title:
--   Two Variable Swap Lemmas: swap two C mul
-- statement:
--   The Two Variable Swap Lemmas construction uses the swap two C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L52-L53

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

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.swap_two_C_mul (a : K) (f : MvPowerSeries (Fin 2) K) : swap2 (C a * f) = C a * swap2 f := by sorry
