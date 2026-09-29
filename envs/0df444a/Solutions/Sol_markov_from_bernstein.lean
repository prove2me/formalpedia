-- Prove2me | solution 1 for markov_from_bernstein
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T09:46:00.842197+00:00
-- url     : https://prove2.me/submissions/613a8ef2-e928-4d79-97fb-7c8e2e4165ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_cheb_pythag
import Theorems.Thm_cheb_deriv_abs_le
import Theorems.Thm_cheb_compare_outer
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

open Polynomial Polynomial.Chebyshev

theorem solution (p : Polynomial ℝ) {d : ℕ} (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → |p.eval c| ≤ (d : ℝ)^2 := by
  intro c hc1 hc2
  have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun hd0 => by omega)
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by positivity
  have hc2_nonneg : (0 : ℝ) ≤ 1 - c^2 := by nlinarith
  by_cases hcase : (d : ℝ)^2 * (1 - c^2) ≤ 1
  · -- Comparison case: |c| near ±1.
    have hcmp := cheb_compare_outer p hd_pos hd h c hc1 hc2 hcase
    calc |p.eval c| ≤ |(derivative (T ℝ (d : ℤ))).eval c| := hcmp
      _ ≤ (d : ℝ)^2 := cheb_deriv_abs_le d c hc1 hc2
  · -- Direct Bernstein case: |c| in the middle.
    push Not at hcase
    have hbern := h c hc1 hc2
    -- (1 - c²) p(c)² ≤ d², and d²(1-c²) > 1, so p(c)² ≤ d²/(1-c²) < d⁴.
    have h1c_pos : (0 : ℝ) < 1 - c^2 := by
      by_contra hle
      push Not at hle
      have : (1 - c^2 : ℝ) = 0 := le_antisymm hle hc2_nonneg
      rw [this, mul_zero] at hcase
      linarith
    have hpc : (p.eval c)^2 ≤ (d : ℝ)^2 / (1 - c^2) := by
      rw [le_div_iff₀ h1c_pos]
      nlinarith [hbern]
    have hdiv : (d : ℝ)^2 / (1 - c^2) < (d : ℝ)^2 * (d : ℝ)^2 := by
      rw [div_lt_iff₀ h1c_pos]
      calc (d : ℝ)^2 = (d : ℝ)^2 * 1 := (mul_one _).symm
        _ < (d : ℝ)^2 * ((d : ℝ)^2 * (1 - c^2)) := by
            apply mul_lt_mul_of_pos_left hcase
            positivity
        _ = (d : ℝ)^2 * (d : ℝ)^2 * (1 - c^2) := by ring
    have hpc2 : (p.eval c)^2 ≤ ((d : ℝ)^2)^2 := by nlinarith [hpc, hdiv]
    have hd2_nonneg : (0 : ℝ) ≤ (d : ℝ)^2 := by positivity
    exact abs_le.mpr (abs_le_of_sq_le_sq' hpc2 hd2_nonneg)
