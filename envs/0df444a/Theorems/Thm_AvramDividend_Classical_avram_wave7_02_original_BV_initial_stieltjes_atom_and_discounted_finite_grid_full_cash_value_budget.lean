-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_stieltjes_atom_and_discounted_finite_grid_full_cash_value_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_initial_stieltjes_atom_and_discounted_finite_grid_full_cash_value_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:39:51.23475+00:00
-- url     : https://prove2.me/theorems/f8f14b92-d457-414b-add4-0bc990a36529
-- title:
--   Original BV complete time-zero Stieltjes dividend plus discounted finite-grid later full right payments and terminal C1 value budget
-- statement:
--   For the actual original BV spectrally negative Levy reserve and the canonical right-dividend HJB jump bound, the exact initial right-payment Stieltjes atom at time zero plus all later complete right-dividend increments along any compact interior monotone time grid, with exponential discounts, and the discounted terminal C1 value are bounded by the initial candidate value plus discounted physical drift cell budgets. This source-specific lemma uses the accepted original time-zero Stieltjes singleton and postpayment HJB value drop and the discounted finite-grid cash/value inequality. It preserves the original X, Ω, filtration, ruinTime and rightLimit D, handles simultaneous jumps via exact path increments and explicitly retains the time-zero mass. First strip exit and passage to the full continuous Stieltjes cash integral remain separate.
-- source:
--   Compose original time-zero atom and value HJB secant 0315346e with original BV finite-partition full right-dividend discount-weighted cash/value budget e814121f. This is a literal original-source finite-grid chain inequality, not the final expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_discounted_full_right_dividend_finite_grid_cash_value_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_initial_stieltjes_atom_and_discounted_finite_grid_full_cash_value_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C) (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|)
    (q : ℝ) (hq : 0 ≤ q)
    (hwnonneg : ∀ y ∈ Icc a b, 0 ≤ w y) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      u 0 = 0 →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      ∀ n,
        rightLimit D 0 ω +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        w x +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by sorry
