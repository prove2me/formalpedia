-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_discounted_full_right_dividend_finite_grid_cash_value_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_stopped_discounted_full_right_dividend_finite_grid_cash_value_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:34:35.598122+00:00
-- url     : https://prove2.me/theorems/e814121f-f7fa-4c50-99bd-8c6e80d114b3
-- title:
--   Original BV stopped C1 finite-grid discount-weighted full right-dividend cash plus terminal value bounded by physical generator drift grid
-- statement:
--   On the genuine spectrally negative bounded-variation Levy source and its actual right-dividend strategy, every monotone finite grid of sampled postpayment reserves in one compact nonnegative C1 strip satisfies a discounted cash-plus-terminal-value inequality. Each full increment of rightLimit D, including all diffuse and singular dividends and simultaneous source/payment jumps between sample times, is weighted by the actual positive discount at the right endpoint. Its sum plus the discounted terminal C1 candidate value is bounded by the initial discounted candidate plus the physical drift integrated as a positive discounted grid sum. This follows from the Proved source-specific pathwise cash-plus-value increment budget and the nonincreasing discount, and is exact for each finite grid without replacing the actual source or claiming the limit Stieltjes identity.
-- source:
--   Finite-partition discounted extension of Proved original source-specific compact full right-dividend pathwise C1 budget 221932c9. The remaining passage to the complete stopped Stieltjes cash expectation and realised compensated source-jump equality is separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_stopped_discounted_full_right_dividend_finite_grid_cash_value_budget
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
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C) (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|)
    (q : ℝ) (hq : 0 ≤ q)
    (hwnonneg : ∀ y ∈ Icc a b, 0 ≤ w y) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      ∀ n,
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        Real.exp (-(q * (u 0 : ℝ))) *
          w (x + X.X (u 0) ω - rightLimit D (u 0) ω) +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by sorry
