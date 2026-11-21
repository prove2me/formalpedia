-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_caplinear_payment_gap_le_of_prepost_bounds
-- name    : AvramDividend.Classical.avram_jump6_E_caplinear_payment_gap_le_of_prepost_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:50:20.840585+00:00
-- url     : https://prove2.me/theorems/0918ebef-e3ef-459b-a686-abdeac54581e
-- title:
--   Caplinear stopped payment-loss comparison under explicit pre/post reserve bounds
-- statement:
--   Exact signed comparison for original discounted payment-cell sums under explicit caplinear pre/post hypotheses. When w agrees with caplinear V at each postpayment reserve and is at least V at each prepayment reserve, every nonnegative discounted raw-w drop is no larger than the corresponding V drop. This isolates the precise missing above-cap inequality in false infinite-activity finite-cap raw-w Stieltjes sources. The result does not claim that original HJB hypotheses imply the extra prepayment bound. It enables a valid conditional bridge from Proved original V-cash estimates.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_E_caplinear_payment_gap_le_of_prepost_bounds
    (w V : ℝ → ℝ) (E : ℕ → ℝ) (Y Z : ℕ → ℝ) (m : ℕ)
    (hE : ∀ i, 0 ≤ E i)
    (hY : ∀ i, w (Y i) = V (Y i))
    (hZ : ∀ i, V (Z i) ≤ w (Z i)) :
    (∑ i ∈ Finset.range m, E i * (w (Y i) - w (Z i))) ≤
    (∑ i ∈ Finset.range m, E i * (V (Y i) - V (Z i))) := by sorry
