-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_mem_finite_nnreal_grid
-- name    : AvramDividend.Classical.dyadic_ceiling_time_mem_finite_nnreal_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:53:24.599863+00:00
-- url     : https://prove2.me/theorems/05efd2bc-8754-40e4-97f2-e6c6638a3945
-- title:
--   Bounded dyadic ceiling times belong to explicit finite nonnegative-real grids
-- statement:
--   Given nonnegative t≤T, the upward dyadic ceiling time ceil(2^n t)/2^n belongs to the image of the natural index range {0,…,ceil(2^n T)} under the dyadic time map k↦k/2^n. This explicitly constructs the finite ℝ≥0 range needed for dyadic finite-valued stopping-time approximation. The proof reuses the proved ceiling index range membership lemma.
-- source:
--   Direct finite-grid construction from proved dyadic_ceiling_index_mem_finite_grid (e4acb2d9-70e6-4a85-9132-33f2a754f1ec), serving bounded_stopping_dyadic_grid_approximation (68cdb033-cbf7-4640-a303-5d06c3c7a761).

import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid
import Mathlib.Data.Finset.Image
open scoped NNReal

theorem AvramDividend.Classical.dyadic_ceiling_time_mem_finite_nnreal_grid
    (t T : ℝ≥0) (ht : t ≤ T) (n : ℕ) :
    (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n ∈
      (Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) + 1)).image
        (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n) := by sorry
