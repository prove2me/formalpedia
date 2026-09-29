-- Prove2me | solution 1 for euler_phi7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:26:55.43469+00:00
-- url     : https://prove2.me/submissions/099958ee-4811-4b56-8c53-752ac64bba9f

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) (h : ¬(7 : ℤ) ∣ a) : (7 : ℤ) ∣ a ^ 6 - 1 := by
  have key : ∀ x : ZMod 7, x ≠ 0 → x ^ 6 = 1 := by decide
  have ha_nz : (a : ZMod 7) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h6 : ((a ^ 6 - 1 : ℤ) : ZMod 7) = 0 := by
    push_cast
    rw [key _ ha_nz, sub_self]
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h6
