-- Prove2me | solution 1 for gpy_integral_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T17:11:33.675577+00:00
-- url     : https://prove2.me/submissions/64a7b4b4-cbf6-4c86-8dd5-91fe29882c9a

/-
  Submission file for the Prove2Me problem `gpy_integral_one_sub_pow`
  (integral of (1-x)^m over [0,1]).

  Self-contained: imports Mathlib only. Top-level `theorem solution`
  is the pure Mathlib statement, proved by the verified reflection
  substitution plus integral_pow. No sorry tactic, no axioms beyond
  the standard ones, no platform imports.
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution (m : ℕ) :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ m = 1 / ((m : ℝ) + 1) := by
  have h := intervalIntegral.integral_comp_sub_mul (f := fun t : ℝ => t ^ m)
    (a := (0 : ℝ)) (b := (1 : ℝ)) (c := (1 : ℝ)) one_ne_zero (d := (1 : ℝ))
  simp only [one_mul, sub_self, sub_zero, inv_one, one_smul] at h
  rw [h, integral_pow]
  simp only [one_pow, zero_pow (show m + 1 ≠ 0 by omega), sub_zero]
