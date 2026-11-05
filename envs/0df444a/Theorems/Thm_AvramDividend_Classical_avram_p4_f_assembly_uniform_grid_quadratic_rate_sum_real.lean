-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_uniform_grid_quadratic_rate_sum_real
-- name    : AvramDividend.Classical.avram_p4_f_assembly_uniform_grid_quadratic_rate_sum_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:42:29.257182+00:00
-- url     : https://prove2.me/theorems/aaeebacb-4613-4f93-8b22-d79bd254276f
-- title:
--   Exact finite-grid chronological cross-count rate factor approaches the second-factorial half rate
-- statement:
--   For any positive number N of equal temporal cells and finite real total marked-jump rate r, the deterministic chronological original-source first-moment product sum Σ_{i=0}^{N-1} (i r/N)(r/N) equals ((N-1)/(2N))r². This is the exact deterministic rate algebra required after the accepted source-physical finite-grid ENNReal expectation theorem 284b2602 and before monotone passage to the original chronological pair mean d938e9a5. This statement makes no claim about random counts or processes; those are supplied by separately proved original-source compensation.
-- source:
--   Pinned Mathlib Finset.sum_range_succ plus induction and ring/field algebra; deterministic rate sub-obligation of original-source chronological second factorial moment d938e9a5.

import Mathlib
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_uniform_grid_quadratic_rate_sum_real
    (N : ℕ) (hN : 0 < N) (r : ℝ) :
    (∑ i ∈ Finset.range N,
      ((i : ℝ) * r / (N : ℝ)) * (r / (N : ℝ))) =
      (((N : ℝ) - 1) / (2 * (N : ℝ))) * r ^ 2 := by sorry
