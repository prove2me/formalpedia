-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_discounted_cash_prefix_finite_mono
-- name    : AvramDividend.Classical.avram_chat24_original_discounted_cash_prefix_finite_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:35:25.272172+00:00
-- url     : https://prove2.me/theorems/ba475fea-8578-4df1-8580-f77f11e665ad
-- title:
--   Original discounted dividend cash has finite monotone strict prefixes
-- statement:
--   For the original Stieltjes dividend measure of a dividend strategy, a nonnegative discount rate and a finite nonnegative full horizon, the real-valued discounted cash on any shorter strict horizon is at most the cash on the full strict horizon. Finite-window discount integrability supplies the finiteness needed by ENNReal.toReal; paymentTimes retains the original initial atom and ruin convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_discounted_cash_prefix_finite_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (s T : ℝ) (hT : 0 ≤ T) (hs : s ≤ T) :
    (∫⁻ t in paymentTimes σ ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes σ ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
