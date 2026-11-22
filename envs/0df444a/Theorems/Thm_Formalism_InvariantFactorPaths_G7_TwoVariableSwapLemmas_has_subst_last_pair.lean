-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_has_subst_last_pair
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.has_subst_last_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:30.726445+00:00
-- url     : https://prove2.me/theorems/214ef7e6-02ac-46f9-baa9-0182f3e506fa
-- title:
--   Two Variable Swap Lemmas: has subst last pair
-- statement:
--   The Two Variable Swap Lemmas construction uses the has subst last pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L160-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L160-L160

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

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.has_subst_last_pair (x : Fin 3) : HasSubst ![(X x : MvPowerSeries (Fin 3) K), X 2] := by sorry
