-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_pow_div
-- name    : Formalism.InvariantFactorPaths.G7.DividedPowerNorms.norm_pow_div
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:29.705791+00:00
-- url     : https://prove2.me/theorems/7c46625b-01f2-4fe5-8d14-7de8a0500dcc
-- title:
--   Divided Power Norms: norm pow div
-- statement:
--   The Divided Power Norms construction uses the norm pow div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/IntegralPderivLgF.lean#L37-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/IntegralPderivLgF.lean#L37-L49

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_natCast
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul

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
open DworkIntegrality (Bd bd_add bd_sub bd_mul bd_C bd_sum int_mul int_pow sm_mul bd_natCast frob_congr
  PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.DividedPowerNorms
variable {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}

theorem Formalism.InvariantFactorPaths.G7.DividedPowerNorms.norm_pow_div (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (m : ℕ) :
    ‖(p : K) ^ (m + 1) / ((m + 1 : ℕ) : K)‖ ≤ (p : ℝ)⁻¹ := by sorry
