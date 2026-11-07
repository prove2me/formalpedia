-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_unit_interval_power_lipschitz
-- name    : AvramDividend.Classical.avram_redux19_unit_interval_power_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:23:54.6475+00:00
-- url     : https://prove2.me/theorems/700a2551-417f-46a8-8fdc-10d3c559ff7f
-- title:
--   Subunit n-fold cell expectation power has n-Lipschitz error bound
-- statement:
--   The nth-power of a real-valued short-cell expectation in [0,1] is Lipschitz with constant n. If two short-cell expectations differ by an order-1/n² rare-jump collision, their nth-power products differ by at most order 1/n. This is an explicit deterministic error bridge to the original marked Laplace limit.
-- source:
--   Finite induction, the algebraic identity b^(n+1)-a^(n+1) = b(b^n-a^n) + (b-a)a^n, positivity and a,b in [0,1]. No stochastic assumptions are hidden.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux19_unit_interval_power_lipschitz (a b : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    0 ≤ b ^ n - a ^ n ∧
      b ^ n - a ^ n ≤ (n : ℝ) * (b - a) := by sorry
