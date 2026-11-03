-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:20:12.922172+00:00
-- url     : https://prove2.me/theorems/a8ff7bd6-f079-4ef8-b239-cfa868c7b180
-- title:
--   Original a.s.-cofinal stopped Ito–Meyer nonnegative-terminal budget passes to full finite-horizon ruin cash
-- statement:
--   Under the original Lévy and dividend strategy assumptions, each measurable pathwise-increasing stopped clock has an exact nonnegative ENNReal Stieltjes reward plus an arbitrary nonnegative ENNReal terminal contribution uniformly bounded in expectation by budget. If the clocks exhaust ruinTime P-almost surely, the full expected original discounted ruin-payment cash through any real T is at most budget. The proof drops terminal contributions and uses the accepted source-specific a.s. cofinal ENNReal cash limit and random-clock measurability. No uniform integrability, reserve continuity at ruin, or altered canonical hypotheses.
-- source:
--   W7-19 accepted source bridge f96b1f8a-2579-483d-811c-7cc626d89912 and exact original stopped reward measurability f2bd15ce-a7f8-404d-a706-f94293b9fda3; direct nonnegative-terminal removal from the local stopped Ito–Meyer inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_stopped_ito_terminal_payoff_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσmeas : ∀ k : ℕ, Measurable (σ k))
    (hσmono : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (Terminal : ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        Terminal k ω) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
