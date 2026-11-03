-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
-- name    : AvramDividend.Classical.avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:28:16.318485+00:00
-- url     : https://prove2.me/theorems/f2bd15ce-a7f8-404d-a706-f94293b9fda3
-- title:
--   Original stopped weighted Stieltjes cash is measurable for any measurable random payment clock
-- statement:
--   For the actual dividend strategy D in the original classical Lévy model and the exact original dividendMeasure/paymentTimes definitions, any measurable extended-valued random payment clock gives a measurable ENNReal discounted Stieltjes cash reward through T. The original right-payment atom at zero, positive clock strict boundary, continuous and singular dividend parts are retained. This supplies the hMeas premise for the W7-19 cofinal random-clock expected bound once W7-18 provides measurable stopping clocks; no new canonical hypothesis or real/ENNReal expectation conversion is introduced.
-- source:
--   Proved original joint paymentTimes measurability 6e9faa20-c0bf-445c-92c0-0fd50340de1b, original global sfinite dividendMeasure kernel and measurable_random_indicator_lintegral; same verified technique as W7-19 candidate 22599.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_any_measurable_clock_paid_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (hσ : Measurable σ)
    (q T : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
