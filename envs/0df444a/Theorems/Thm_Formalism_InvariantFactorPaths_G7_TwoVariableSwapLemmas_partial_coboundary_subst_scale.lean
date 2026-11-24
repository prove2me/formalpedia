-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_partial_coboundary_subst_scale
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_subst_scale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:57.492818+00:00
-- url     : https://prove2.me/theorems/3f9be8e5-f7fd-4924-b8c9-8caf1d144292
-- title:
--   Two Variable Swap Lemmas: partial coboundary subst scale
-- statement:
--   The Two Variable Swap Lemmas construction uses the partial coboundary subst scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L177-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L177-L200

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

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_subst_scale {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) {u : K} (v : K)
    (hu : subst (fun a : Fin 2 => C u * (X a : MvPowerSeries (Fin 2) K)) F = C u * F)
    (H : MvPowerSeries (Fin 2) K) :
    d1 F (subst (sc2 u v) H) = subst (sc3 u v) (d1 F H) := by sorry
