-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_finite_grid_factorial_collision_sandwich
-- name    : AvramDividend.Classical.avram_mixed_source13_finite_grid_factorial_collision_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:44:52.993149+00:00
-- url     : https://prove2.me/theorems/43e4d0f0-3e58-4e71-a9d9-8b985befde70
-- title:
--   Original finite-grid factorial pairs bounded by full-cutoff diagonal
-- statement:
--   For each physical finite grid, natural annulus cell counts are bounded by corresponding counts of the original full-upper-cutoff negative jumps. The factorial count of the total annulus cells lies between twice the chronological cross-cell product and that product plus the sum of full-cutoff same-cell factorials. This is the deterministic collision estimate needed by original uniform-grid sandwich d924a79e and original annulus second moment 6ea0212e, with no stochastic assumptions.
-- source:
--   Source-faithful necessary algebraic diagonal domination for original finite-grid annulus factorial sandwich d924a79e. Reuses Proved f56b2229 finite-grid factorial telescoping.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_finite_grid_factorial_telescoping_real
open BigOperators AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_finite_grid_factorial_collision_sandwich
    (k : ℕ) (a b : ℕ → ℕ) (hab : ∀ i, a i ≤ b i) :
    let A : ℕ → ℝ := fun i => a i
    let C : ℕ → ℝ := fun i => b i
    let S : ℝ := ∑ i ∈ Finset.range k, A i
    let H : ℝ := 2 * (∑ i ∈ Finset.range k,
      (∑ j ∈ Finset.range i, A j) * A i)
    H ≤ S * (S - 1) ∧
      S * (S - 1) ≤ H + (∑ i ∈ Finset.range k, C i * (C i - 1)) := by sorry
