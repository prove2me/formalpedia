-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ruin_clock_localized_cash_fatou_no_ui
-- name    : AvramDividend.Classical.avram_sweep16_original_ruin_clock_localized_cash_fatou_no_ui
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:00:03.610287+00:00
-- url     : https://prove2.me/theorems/da912121-b462-4dd4-948d-d8477e20d713
-- title:
--   Original bounded ruin-clock localized cash Fatou bound without stopped-martingale uniform integrability
-- statement:
--   A source-exact Fatou reduction for the same original Lévy process, dividend strategy, discount and natural ruin-truncated clock: if measurable localized discounted cash rewards have a common expectation bound, and the original stopped cash is a.s. below their liminf, then its expectation inherits that bound. This does not assume uniform integrability or zero expectation for the unlocalized stochastic residual; the genuine localized budgets and original-cash liminf relation remain explicit source obligations.
-- source:
--   Exact SWEEP16 canonical 750ad13b natural stopped clock, source cash from dividendMeasure and paymentTimes; pinned Mathlib MeasureTheory.lintegral_liminf_le; bounded-localisation alternative required by the original verification closure.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_ruin_clock_localized_cash_fatou_no_ui
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ k, Measurable (LocalCash k))
    (hLocalBudget : ∀ k,
      (∫⁻ ω, LocalCash k ω ∂P) ≤ ENNReal.ofReal (w x))
    (hCashLiminf : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      Filter.liminf (fun k : ℕ => LocalCash k ω) Filter.atTop) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
