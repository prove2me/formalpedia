-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_exp_log_scale_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:32:11.923115+00:00
-- url     : https://prove2.me/theorems/1c71a04d-268a-4126-b1bd-c0537bda0db1
-- title:
--   Genuine uncapped first-record discount equals exp(-height times ordinary q-scale logarithmic slope)
-- statement:
--   For the actual original-process first strict upward record time T_h and actual reflected drawdown ruin time D_a, pure infinite-small-jump variation, positive q, a and h, the real discounted first-record mass is exactly exp(-h W'(a)/W(a)). Both W'(a) and W(a) are ordinary real quantities, with W positive and continuously differentiable by the genuinely established Standing-free first-record route. This is the quantitative original-process fluctuation identity underlying the pure-jump q-scale C1 proof, with no Esscher/excursion substitution.
-- source:
--   Actual original record exponential hazard 1f5b13d3, proved logarithmic derivative identification 30843a7a, Stand-free pure-jump C1 cd61d678, positive W e50526dc, HasDerivAt.log.

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_eq_log_scale_deriv

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_exp_log_scale_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal =
      Real.exp (-(h * (deriv W a / W a))) := by sorry
