-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_two_sums
-- name    : Formalism.InvariantFactorPaths.G7.TwoS.cg_two_sums
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:14.663395+00:00
-- url     : https://prove2.me/theorems/7a5ae948-958b-4d4e-ba7e-e52681069d10
-- title:
--   Two S: cg two sums
-- statement:
--   The Two S construction uses the cg two sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L571-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TheoremSFromKOneOf.lean#L571-L598

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ} [NeZero ν]

theorem Formalism.InvariantFactorPaths.G7.TwoS.cg_two_sums {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {om oms : Fin ν → ZMod (2 * ν) → K} (hO : OmOK p ν om oms) {c c' : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖c'‖ ≤ 1) {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0)
    (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) :
    Cg p (MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c'))
      (hhS p (uS c c')) := by sorry
