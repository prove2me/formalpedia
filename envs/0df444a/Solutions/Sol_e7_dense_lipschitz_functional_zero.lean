-- Prove2me | solution 1 for e7_dense_lipschitz_functional_zero
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:53:12.480941+00:00
-- url     : https://prove2.me/submissions/5920e50c-8d6d-4078-b8bf-8dc648568374

import Mathlib

open MeasureTheory Set Filter

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Submodule ℝ V) (S : Set V) (F : V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (happrox : ∀ x : L, ∀ ε : ℝ, 0 < ε →
      ∃ y, y ∈ S ∧ ‖(x : V) - y‖ < ε)
    (hLip : ∀ x y, ‖F x - F y‖ ≤ C * ‖x - y‖)
    (hzero : ∀ y, y ∈ S → F y = 0) :
    ∀ x : L, F x = 0 := by
  intro x
  have hnorm : ‖F x‖ = 0 := by
    by_contra hne
    have hne' : F (x : V) ≠ 0 := by
      intro h; exact hne (by simp [h])
    have hpos : 0 < ‖F (x : V)‖ := norm_pos_iff.mpr hne'
    obtain ⟨y, hyS, hy⟩ := happrox x (‖F (x : V)‖ / (2 * (C + 1))) (by positivity)
    have hle : ‖F (x : V)‖ ≤ C * ‖(x : V) - y‖ := by
      have := hLip (x : V) y
      rwa [hzero y hyS, sub_zero] at this
    rcases eq_or_lt_of_le hC with hC0 | hCpos
    · rw [← hC0, zero_mul] at hle
      linarith
    · have hstep : C * ‖(x : V) - y‖ < C * (‖F (x : V)‖ / (2 * (C + 1))) :=
        mul_lt_mul_of_pos_left hy hCpos
      have hbound : C * (‖F (x : V)‖ / (2 * (C + 1))) ≤ ‖F (x : V)‖ / 2 := by
        have hfrac : C / (C + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        have heq : C * (‖F (x : V)‖ / (2 * (C + 1))) =
            (C / (C + 1)) * (‖F (x : V)‖ / 2) := by
          field_simp
        rw [heq]
        exact mul_le_of_le_one_left (by positivity) hfrac
      linarith
  exact norm_eq_zero.mp hnorm
