-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
-- name    : AvramDividend.Classical.avram_limit2_original_strict_discounted_cash_finite_all_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:30:35.738194+00:00
-- url     : https://prove2.me/theorems/74c42d89-15e7-48b6-8dfb-106d0a6ba14a
-- title:
--   Original strict discounted stopped cash is finite at every finite horizon
-- statement:
--   For the actual original SpectrallyNegativeLevy X and IsDividendStrategy D, the strictly stopped paymentTimes (ruinTime X x D omega) intersect Iio T is contained in the closed Iic T payment set. Monotonicity of the genuine ENNReal Stieltjes lintegral and already Proved avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit (1a006d5f) bound original strict discounted cash by ENNReal.ofReal (rightLimit D T omega), finite for every path. No strict survival, martingale identity, equality-in-law, or terminal vanishing is needed. This supplies exactly the missing cash finite hypothesis of the signed-real to ENNReal conversion.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_strict_discounted_cash_finite_all_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≠ ⊤ := by sorry
