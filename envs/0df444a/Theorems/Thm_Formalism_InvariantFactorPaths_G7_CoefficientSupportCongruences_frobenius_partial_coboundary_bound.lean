-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_frobenius_partial_coboundary_bound
-- name    : Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.frobenius_partial_coboundary_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:55.213809+00:00
-- url     : https://prove2.me/theorems/a40f648d-4f05-42ff-8e37-6d1e9041a9a5
-- title:
--   Coefficient Support Congruences: frobenius partial coboundary bound
-- statement:
--   The Coefficient Support Congruences construction uses the frobenius partial coboundary bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L207-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L207-L411

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

theorem Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.frobenius_partial_coboundary_bound {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    {σ : K →+* K} (hU : UnrOK K p σ) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog p F)
    {G : MvPowerSeries (Fin 2) K} {c : K} (hc : ‖c‖ ≤ 1) (hDer : DerivIs p G c)
    (hΔ : d1 F (DeS p σ G) =
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p))) :
    Bd (p : ℝ)⁻¹ (frobVar p (MvPowerSeries.map σ (d1 F G)) -
      MvPowerSeries.C (p : K) * d1 F G) := by sorry
