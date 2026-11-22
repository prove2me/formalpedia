-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_coeff_subst_scale_two
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_subst_scale_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:46.525812+00:00
-- url     : https://prove2.me/theorems/540238a7-eb60-4748-9577-da70ca3c9868
-- title:
--   Two Variable Swap Lemmas: coeff subst scale two
-- statement:
--   The Two Variable Swap Lemmas construction uses the coeff subst scale two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L128-L131

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

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_subst_scale_two (u v : K) (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) :
    coeff n (subst (sc2 u v) H) = u ^ n 0 * v ^ n 1 * coeff n H := by sorry
