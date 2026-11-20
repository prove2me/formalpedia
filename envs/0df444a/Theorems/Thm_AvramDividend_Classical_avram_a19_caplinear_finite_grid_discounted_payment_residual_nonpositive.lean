-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_caplinear_finite_grid_discounted_payment_residual_nonpositive
-- name    : AvramDividend.Classical.avram_a19_caplinear_finite_grid_discounted_payment_residual_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:49:20.796992+00:00
-- url     : https://prove2.me/theorems/884f45f5-51a4-4668-94aa-9f74fd064fa9
-- title:
--   Finite discounted physical dividend grid cap-linear residual is nonpositive
-- statement:
--   For a finite collection of original physical right-dividend cells, let Y_i be each nonnegative postpayment reserve below the cap, D_i its nonnegative payment increment, and E_i its nonnegative discount. If the original HJB gradient ≥1 is encoded by the interior secant lower bound from each Y_i to the cap, then the sum of all discounted cap-linear dividend payment residuals is ≤0, including prepayment cap crossings. This is the full finite-grid dividend sign needed in the stopped Itô ledger. It does not assume martingale centring or ruin-contact limits.
-- source:
--   Exact scalar original finite-cap caplinear extension applied to every right dividend atom in a Finset grid; sums nonpositive weighted cells.

import Mathlib

/-- Summing every original finite-cap right-dividend payment cell gives a nonpositive discounted residual. -/
theorem AvramDividend.Classical.avram_a19_caplinear_finite_grid_discounted_payment_residual_nonpositive
    {ι : Type*} (s : Finset ι) (w : ℝ → ℝ) (C : ℝ)
    (Y D E : ι → ℝ)
    (hY : ∀ i ∈ s, Y i ≤ C)
    (hD : ∀ i ∈ s, 0 ≤ D i)
    (hE : ∀ i ∈ s, 0 ≤ E i)
    (hSlope : ∀ i ∈ s, ∀ z : ℝ,
      Y i ≤ z → z ≤ C → z - Y i ≤ w z - w (Y i)) :
    (∑ i ∈ s, E i * (D i + w (Y i) -
      (if Y i + D i ≤ C then w (Y i + D i)
       else w C + (Y i + D i - C)))) ≤ 0 := by sorry
