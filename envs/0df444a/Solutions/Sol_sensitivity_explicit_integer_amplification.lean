-- Prove2me | solution 1 for sensitivity_explicit_integer_amplification
-- status  : ACCEPTED   (prove)
-- author  : @spongeboi
-- created : 2026-11-14T08:36:38.581602+00:00
-- url     : https://prove2.me/submissions/1651d269-fded-4123-82b0-c7f412e6e703

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

set_option autoImplicit false

private theorem absorb_constant (A B C : ℕ) (hA : 0 < A) (hAB : A < B) :
    C * A ^ (C * A + 1) < B ^ (C * A + 1) := by
  have hbern :
      A ^ (C * A + 1) + (C * A + 1) * A ^ (C * A) ≤
        (A + 1) ^ (C * A + 1) := by
    simpa using
      (pow_add_mul_le_add_pow (a := A) (b := (1 : ℕ))
        (Nat.zero_le A) (by omega) (C * A + 1))
  have hstrict :
      C * A ^ (C * A + 1) <
        A ^ (C * A + 1) + (C * A + 1) * A ^ (C * A) := by
    rw [pow_succ]
    nlinarith [pow_pos hA (C * A)]
  have hmono : (A + 1) ^ (C * A + 1) ≤ B ^ (C * A + 1) :=
    Nat.pow_le_pow_left (by omega) _
  exact hstrict.trans_le (hbern.trans hmono)

theorem solution (C R G p q : ℕ) (hR : 0 < R) (hgap : R ^ p < G ^ q) :
    (C * R ^ (C ^ p * R ^ p + 1)) ^ p <
      (G ^ (C ^ p * R ^ p + 1)) ^ q := by
  have h := absorb_constant (R ^ p) (G ^ q) (C ^ p) (pow_pos hR p) hgap
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using h
