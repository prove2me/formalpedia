-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_partial_coboundary_de_s_g_series
-- name    : Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.partial_coboundary_de_s_g_series
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:42.552796+00:00
-- url     : https://prove2.me/theorems/85ed82e5-51f0-4901-8f0b-510346b88336
-- title:
--   Coefficient Support Congruences: partial coboundary de s g series
-- statement:
--   The Coefficient Support Congruences construction uses the partial coboundary de s g series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L166-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FrobeniusPartialCoboundaryBound.lean#L166-L180

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
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.partial_coboundary_de_s_g_series {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) (σ : K →+* K) {c : K}
    (hσσ : σ (σ c) = c) {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hl : cob F (lgF K p) = 0) :
    d1 F (DeS p σ (Gser p c (σ c))) =
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) := by sorry
