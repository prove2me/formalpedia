-- Prove2me | solution 1 for flt7_fermat_little
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:47:57.15156+00:00
-- url     : https://prove2.me/submissions/5acfcf9e-4d32-4130-a726-3ebe0d1d3a87

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic

-- Fermat's Little Theorem for exponent 7: 7 | a^7 - a for all integers a.
theorem solution (a : ℤ) : (7 : ℤ) ∣ a^7 - a := by
  have hmod : ∀ x : ZMod 7, x^7 = x := by decide
  have h2 : ((a^7 - a : ℤ) : ZMod 7) = 0 := by
    push_cast
    rw [hmod]
    exact sub_self _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a^7 - a) 7).mp h2
