-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_local_sum_bound
-- name    : AvramDividend.Classical.causal_geometric_neumann_local_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:29:30.154916+00:00
-- url     : https://prove2.me/theorems/87b4d0cc-d2e2-4ac0-8735-e49c4d9f4a9e
-- title:
--   Geometric Neumann term bounds imply local uniform finite-sum bounds
-- statement:
--   A geometric bound on each Gaussian Neumann correction uniform over a fixed finite time interval yields a single bound for all Neumann partial sums on that interval. Combined with the local convolution-majorant bridge, this supplies the dominated-convergence envelope.
-- source:
--   Apply Mathlib norm_sum_le_of_le and geom_sum_of_lt_one to convert an interval-uniform estimate |Q_n(s)|≤C_x ρ^n for 0≤ρ<1 into an n-independent bound C_x/(1−ρ). This supplies the local boundedness premise of causal_local_neumann_convolution_majorant in the Gaussian C1 derivative-resolvent construction.

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Exponential

open Real Set

theorem AvramDividend.Classical.causal_geometric_neumann_local_sum_bound
    (Q : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hQ : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖Q n s‖ ≤ C * ρ ^ n) :
    ∀ x : ℝ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ m : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖(∑ i ∈ Finset.range (m + 1), Q i) s‖ ≤ D := by sorry
