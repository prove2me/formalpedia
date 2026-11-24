-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_partial_coboundary_g_series_equiv
-- name    : Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.partial_coboundary_g_series_equiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:54.954842+00:00
-- url     : https://prove2.me/theorems/05ed8e04-c70d-45c4-afc3-80c51ce29046
-- title:
--   Coefficient Support Congruences: partial coboundary g series equiv
-- statement:
--   The Coefficient Support Congruences construction uses the partial coboundary g series equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L413-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L413-L437

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow

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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution

theorem Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.partial_coboundary_g_series_equiv {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    {σ : K →+* K} (hU : UnrOK K p σ) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog p F)
    {c : K} (hc : ‖c‖ ≤ 1) (hσσ : σ (σ c) = c) : Simeq (d1 F (Gser p c (σ c))) 0 := by sorry
