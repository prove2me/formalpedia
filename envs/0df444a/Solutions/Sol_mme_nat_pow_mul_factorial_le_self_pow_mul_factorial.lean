-- Prove2me | solution 1 for mme_nat_pow_mul_factorial_le_self_pow_mul_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:19:57.159433+00:00
-- url     : https://prove2.me/submissions/442a1e35-bc92-413b-9cdd-4504db9f3140

import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

/-- For a fixed natural weight `w`, the integer sequence `w^a / a!`
is maximized at `a = w` (with the usual adjacent tie at `w - 1`).  The
division-free form is convenient for multinomial coefficient comparisons. -/
theorem solution (w a : ℕ) :
    w ^ a * w.factorial ≤ w ^ w * a.factorial := by
  rcases le_total a w with haw | hwa
  · have hdesc : w.factorial ≤ a.factorial * w ^ (w - a) := by
      have hfac :=
        Nat.factorial_mul_descFactorial (n := w) (k := w - a)
          (Nat.sub_le w a)
      calc
        w.factorial = a.factorial * w.descFactorial (w - a) := by
          simpa only [Nat.sub_sub_self haw] using hfac.symm
        _ ≤ a.factorial * w ^ (w - a) :=
          Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow w (w - a))
    calc
      w ^ a * w.factorial ≤ w ^ a * (a.factorial * w ^ (w - a)) :=
        Nat.mul_le_mul_left _ hdesc
      _ = (w ^ a * w ^ (w - a)) * a.factorial := by ac_rfl
      _ = w ^ (a + (w - a)) * a.factorial := by rw [Nat.pow_add]
      _ = w ^ w * a.factorial := by rw [Nat.add_sub_of_le haw]
  · have htail : w.factorial * w ^ (a - w) ≤ a.factorial :=
      Nat.factorial_mul_pow_sub_le_factorial hwa
    calc
      w ^ a * w.factorial =
          w ^ w * (w.factorial * w ^ (a - w)) := by
            calc
              w ^ a * w.factorial =
                  (w ^ w * w ^ (a - w)) * w.factorial := by
                    rw [← Nat.pow_add, Nat.add_sub_of_le hwa]
              _ = w ^ w * (w.factorial * w ^ (a - w)) := by ac_rfl
      _ ≤ w ^ w * a.factorial := Nat.mul_le_mul_left _ htail
