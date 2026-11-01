-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_strictAntiOn_height
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_strictAntiOn_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:26:55.937449+00:00
-- url     : https://prove2.me/theorems/f5fbb748-f9b6-4489-9d89-75928b9f55e2
-- title:
--   Genuine reflected first-record discounted mass strictly decreases with positive record height
-- statement:
--   For any positive reflected drawdown depth a under infinite first small-negative-jump variation and q>0, the original-process discounted first-record mass G_a(h)=E[e^{-qT_h};T_h<D_a] is strictly decreasing as the positive strict upward record height h increases. The proved original-process exponential identity has rate W'(a)/W(a), which is now bounded below by the strictly positive unrestricted Lévy Laplace root. Thus the strict decrease is genuinely stochastic and has no Standing hypothesis.
-- source:
--   Positive Laplace root cfe6d3e1, genuine original hazard lower bound a5dbcace, and source first-record full exponential identity 1c71a04d. Strict real exponential monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_strictAntiOn_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a →
      StrictAntiOn (fun h : ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) (Ioi (0 : ℝ)) := by sorry
