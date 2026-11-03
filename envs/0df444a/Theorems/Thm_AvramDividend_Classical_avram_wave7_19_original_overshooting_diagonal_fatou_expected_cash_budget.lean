-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_diagonal_fatou_expected_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_overshooting_diagonal_fatou_expected_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:44:36.491146+00:00
-- url     : https://prove2.me/theorems/7d8962b1-c1e2-4eff-a485-9548fbeee31a
-- title:
--   Original nonmonotone overshooting diagonal Fatou expectation bridge needs only liminf of stopped budgets
-- statement:
--   A diagonal jump-truncation/localisation sequence need not provide uniform expected bounds at each finite clock. For the original Lévy and dividend strategy, measurable clocks with P-a.s. liminf at least ruin and liminf of their exact expected stopped ENNReal Stieltjes payments ≤budget already imply the full expected ruin cash bound. On the good source event, full pathwise cash≤liminf of stopped cash by W7-19's exact pathwise paymentTimes Fatou lemma. The tail infima of cash are measurable and monotone in n; lintegral_iSup and nonnegative integral monotonicity bound E(liminf cash) by liminf(E cash). This supports stochastic approximations with only asymptotically vanishing errors, no per-clock uniform epsilon, no UI, and exact boundary/initial atom semantics.
-- source:
--   W7-19 new original pathwise overshooting cash≤liminf 5c7cbb46-c13a-4b75-981e-5eae72c6b358 when Proved; original random-clock cash measurable f2bd15ce-a7f8-404d-a706-f94293b9fda3; exact Mathlib lintegral_iSup and tail infima monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_overshooting_diagonal_fatou_expected_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminfLower : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (budget : ℝ≥0∞)
    (hBudgetLiminf :
      (⨆ n : ℕ, ⨅ k : ℕ,
        (∫⁻ ω, (∫⁻ t in paymentTimes (τ (n + k) ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P)) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
