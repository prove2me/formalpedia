-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_discounted_full_payment_grid_negative_value_residual
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_discounted_full_payment_grid_negative_value_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:33:00.339549+00:00
-- url     : https://prove2.me/theorems/655d3e6f-127d-4c99-88bc-b2ca6d38b6f5
-- title:
--   Original BV full right-dividend discounted grid with an exact negative candidate-value residual instead of a nonnegativity assumption
-- statement:
--   For the actual bounded-variation spectrally negative Levy reserve and its original right-dividend strategy, every compact C1 grid admits a discounted full right-dividend cash plus terminal candidate value budget, without assuming w nonnegative anywhere. The only addition to the physical drift cell bound is an explicit nonnegative time-discount residual at sampled states: each discount drop multiplied by max(0,-w(Y_i)). This is the exact obstruction to the usual nonnegative-value discount step and vanishes under canonical sampled terminal positivity. The theorem preserves all negative source and simultaneous/right dividend increments through the actual original reserve and is a finite-grid step toward stopped Stieltjes HJB verification.
-- source:
--   Adapt the Proved 221932c9 actual source C1 path increment with a signed exact discount-value correction, replacing e814's global nonnegativity assumption by the precisely quantified negative-part residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_compact_stopped_full_right_dividend_C1_pathwise_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_discounted_full_payment_grid_negative_value_residual
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
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) +
        (∑ i ∈ Finset.range n,
          (Real.exp (-(q * (u i : ℝ))) -
            Real.exp (-(q * (u (i + 1) : ℝ)))) *
            max 0 (-(w (x + X.X (u i) ω - rightLimit D (u i) ω)))) := by sorry
