-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_ubv_ruin_clock_outer_mct_bridge
-- name    : AvramDividend.Classical.avram_wave7_19_ubv_ruin_clock_outer_mct_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:51:24.745249+00:00
-- url     : https://prove2.me/theorems/c59c4db0-7b8e-4587-a21c-54aa05e0d33d
-- title:
--   Original UBV finite-clock cash budgets pass to the full pre-ruin horizon by outer MCT
-- statement:
--   A source-exact monotone convergence bridge for the genuine discounted Stieltjes dividend cash, with its required measurability, monotonicity and pathwise exhaustion obligations exposed. Uniform finite-clock ENNReal expectation bounds imply the full finite-horizon cash bound. W7-08 must discharge the hypotheses from original admissible controls, W7-19's clock-domain lemma and its local stopped Ito inequality; no new assumption is added to the canonical statement.
-- source:
--   Exact original cash function from source dividendMeasure and paymentTimes; pinned Mathlib MeasureTheory.lintegral_iSup has hypotheses Measurable and Monotone. Discharges final outer passage from finite integer clocks without assuming strong uniform integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_ubv_ruin_clock_outer_mct_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω => (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))))
    (hMono : Monotone (fun n : ℕ => fun ω : Ω => (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))))
    (hLimit : ∀ ω : Ω, (⨆ n : ℕ, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hBudget : ∀ n : ℕ, (∫⁻ ω, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
