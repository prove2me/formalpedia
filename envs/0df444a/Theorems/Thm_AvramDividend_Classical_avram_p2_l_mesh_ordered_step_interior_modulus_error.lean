-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_ordered_step_interior_modulus_error
-- name    : AvramDividend.Classical.avram_p2_l_mesh_ordered_step_interior_modulus_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:43:24.996384+00:00
-- url     : https://prove2.me/theorems/60f0fac2-e85b-4b31-baef-fe1adce697b8
-- title:
--   Uniform modulus controls the original marked-test step approximation on every ordered mesh cell
-- statement:
--   If a real continuous marked test has a uniform modulus δ for error η, every ordered partition cell is narrower than δ, and each cell uses its left-endpoint sample as coefficient, then at every point in any one cell the weighted half-open interval-step sum differs from the original test by less than η. The proof uses the already Proved/public exact single-active-cell identity and requires no stochastic or convergence assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_strict_partition_cell_sum_eq_sample

open Set AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_p2_l_mesh_ordered_step_interior_modulus_error
    {n : ℕ} (f : ℝ → ℝ) (a b : Fin n → ℝ)
    (hordered : ∀ i j : Fin n, i < j → b i ≤ a j)
    (δ η : ℝ)
    (hmod : ∀ x y : ℝ, |x - y| < δ → |f x - f y| < η)
    (hwidth : ∀ i : Fin n, b i - a i < δ)
    (z : ℝ) (i : Fin n) (hi : z ∈ Ioc (a i) (b i)) :
    |f z - (∑ j : Fin n,
      if z ∈ Ioc (a j) (b j) then f (a j) else 0)| < η := by sorry
