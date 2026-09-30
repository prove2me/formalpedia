-- Prove2me | solution 1 for polynomial_grid_continuous_extension
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T00:38:44.557584+00:00
-- url     : https://prove2.me/submissions/b5e228d6-810c-4b46-98e9-390a2dea963f

import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Polynomial

theorem solution : ¬ (∀ {b : ℕ} (Q : Polynomial ℝ) {d : ℕ},
    Q.natDegree ≤ d →
    (∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1) →
    2 * d ^ 2 ≤ b →
    ∀ x : ℝ, 0 ≤ x → x ≤ (b : ℝ) → |Q.eval x| ≤ 1) := by
  intro h
  let Q : Polynomial ℝ := C (1 / 36) * X ^ 2 - C (17 / 36) * X + C 1
  have hdeg : Q.natDegree ≤ 2 := by
    dsimp [Q]
    compute_degree!
  have hgrid : ∀ t : ℕ, t ≤ 17 → |Q.eval (t : ℝ)| ≤ 1 := by
    intro t ht
    interval_cases t <;> norm_num [Q]
  have hbad := h (b := 17) Q (d := 2) hdeg hgrid (by decide)
    (17 / 2) (by norm_num) (by norm_num)
  norm_num [Q] at hbad

#print axioms solution
