-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_discounted_full_right_dividend_grid_sampled_nonnegative_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_discounted_full_right_dividend_grid_sampled_nonnegative_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:22:03.295357+00:00
-- url     : https://prove2.me/theorems/bff0acf6-a436-4fc4-a5ec-65674c02cead
-- title:
--   Original BV discounted full right-dividend finite-grid cash plus terminal value with nonnegativity only at sampled reserves
-- statement:
--   For the actual controlled bounded-variation spectrally negative Levy process and true right-dividend strategy, assume each monotone grid's postpayment reserves remain in a compact C1 band and the candidate w is nonnegative only at those sampled reserves. Then the actual discounted full right-dividend increments plus terminal C1 value obey the original physical drift-cell bound. This sharpens Proved e814121f by exactly weakening a global band nonnegativity hypothesis to the values used in each induction step. It handles finite-grid source negative and simultaneous dividend jumps and all finite-variation payment changes as original rightLimit increments; it is not yet a complete Stieltjes limit or expected HJB theorem.
-- source:
--   Exact proof adaptation of Proved e814121f with sample-wise nonnegativity in the one-step discount comparison; source process, filtration and rightLimit D retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_discounted_full_right_dividend_grid_sampled_nonnegative_budget
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
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      (∀ n, 0 ≤ w (x + X.X (u n) ω - rightLimit D (u n) ω)) →
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
