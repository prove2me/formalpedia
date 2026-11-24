-- Prove2me | solution 1 for pattern_nContinuant1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:09:22.78133+00:00
-- url     : https://prove2.me/submissions/ea6f75ea-985a-469e-b9a2-cc1bc3fe324c

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Definitions.Def_FriezePatterns_chapter1

set_option autoImplicit true

theorem _root_.solution (F : Type*) [Field F] (f : ℕ×ℕ → F) (n: ℕ) [nzPattern_n F f n] : ∀ i, i ≤ n-1 → ∀m, f (i+2,m) = f (2,m+i)*f (i+1,m) - f (i,m) := by
  intro i
  induction i with
  | zero =>
  simp
  intro m
  have h₀ : f (0, m) = 0 := pattern_n.topBordZeros n m
  have h₁ : f (1, m) = 1 := pattern_n.topBordOnes n m
  rw [h₀, h₁]
  simp
  | succ k ih =>
  intro h m
  have h' : 1 ≤ k+1 ∧ k+1 ≤ n := by omega
  have hh' : k ≤ n-1 := by omega
  have ih₁ : f (k + 2, m + 1) = f (2, m + 1 + k) * f (k + 1, m + 1) - f (k, m + 1) := ih hh' (m+1)
  have h₂ : f (k + 1, m + 1) ≠ 0 := nzPattern_n.non_zero (k+1) (m+1) h'
  have h₃ : f (k + 3, m) * f (k + 1, m + 1) = (f (k + 2, m) * f (2, m + k + 1) - f (k + 1, m)) * f (k + 1, m + 1) :=
    calc f (k + 3, m) * f (k + 1, m + 1) = f (k + (2+1), m) * f (k + 1, m + 1) := by rw [two_add_one_eq_three]
      _= f ((k + 1) + 2, m) * f (k + 1, m + 1) := by congr
      _= f ((k + 1)+1, m) * f ((k + 1)+1, m + 1) - 1 := by rw [← pattern_n.diamond (k+1) m h]
      _= f ((k + 1)+1, m) * f (k + 2, m + 1) - 1 := by simp
      _= f (k + 2, m) * (f (2, m + 1 + k) * f (k + 1, m + 1) - f (k, m + 1)) - 1 := by rw [ih₁]
      _= f (k + 2, m) * (f (2, m + k + 1) * f (k + 1, m + 1) - f (k, m + 1)) - 1 := by rw [add_right_comm]
      _= f (k + 2, m) * (f (2, m + k + 1) * f (k + 1, m + 1)) - f (k + 2, m) * f (k, m + 1) - 1 := by rw [mul_sub_left_distrib]
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - (f (k + 2, m) * f (k, m + 1) + 1) := by rw [mul_assoc, sub_sub]
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - (f (k + 1, m) * f (k + 1, m + 1) - 1 + 1) := by rw [← pattern_n.diamond k m hh']
      _= f (k + 2, m) * f (2, m + k + 1) * f (k + 1, m + 1) - f (k + 1, m) * f (k + 1, m + 1) := by rw [add_comm_sub, sub_self, add_zero]
      _= (f (k + 2, m) * f (2, m + k + 1) - f (k + 1, m)) * f (k + 1, m + 1) := by rw [← sub_mul]
  rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega,
      show m + (k + 1) = m + k + 1 by omega,
      ← mul_inv_cancel_right₀ h₂ (f (k + 3, m)),
      mul_inv_eq_iff_eq_mul₀ h₂, mul_comm (f (2, m + k + 1))]
  exact h₃
