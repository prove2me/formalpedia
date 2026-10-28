-- Prove2me | solution 1 for gpy_cutoff_not_mul
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T19:54:17.867176+00:00
-- url     : https://prove2.me/submissions/19806360-589e-4c1e-9e51-90f7e325f5a6

/-
  Submission file for the Prove2Me problem `gpy_cutoff_not_mul`
  (Selberg cutoff does not factor over sums).

  Self-contained: imports Mathlib only. Top-level `theorem solution`
  in the problem's exact binder/statement form (statement mechanically
  extracted from the restated theorem, so the two are textually
  identical). The proof is the original proof of `cutoff_not_mul`
  from GPYEulerProd.lean, verbatim.

  SCOPE, stated honestly (exactly as the source header): this proves
  the polynomial identity fails at s₁ = s₂ = 1/2 for deg ≥ 1; it does
  NOT by itself refute cutoff factorization on the integer lattice
  (that would need transcendence results about logarithms of integers,
  which are not claimed here).
  No sorry tactic, no axioms beyond the standard ones, no platform
  imports.
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {deg : ℕ} (hdeg : 1 ≤ deg) :
    (1 - ((1 : ℝ) / 2 + (1 : ℝ) / 2)) ^ deg ≠
      (1 - (1 : ℝ) / 2) ^ deg * (1 - (1 : ℝ) / 2) ^ deg := by
  have h1 : (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1 := by norm_num
  rw [h1]
  simp only [sub_self]
  rw [zero_pow (by omega : deg ≠ 0)]
  have hpos : (0 : ℝ) < (1 - (1 : ℝ) / 2) ^ deg * (1 - (1 : ℝ) / 2) ^ deg := by
    apply mul_pos <;> apply pow_pos <;> norm_num
  exact (ne_of_gt hpos).symm

#print axioms solution
