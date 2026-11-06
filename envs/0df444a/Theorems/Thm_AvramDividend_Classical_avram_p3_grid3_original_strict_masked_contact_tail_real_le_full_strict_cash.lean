-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
-- name    : AvramDividend.Classical.avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:57:37.651992+00:00
-- url     : https://prove2.me/theorems/efabc067-fc7b-40cf-9347-757696a0fe6b
-- title:
--   Original real discounted strict contact-tail cash is bounded by the full actual strict horizon cash
-- statement:
--   For actual original SpectrallyNegativeLevy X and dividendMeasure D, any strict shrinking contact interval below tau≤T is a subset of the literal strict Iio T payment set. The infinite integral is monotone, and finite original full strict cash allows monotonicity through ENNReal.toReal. This gives an unconditional pathwise domination by the already proved integrable original strict cash.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T) (δ : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((τ : ℝ) - δ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal := by sorry
