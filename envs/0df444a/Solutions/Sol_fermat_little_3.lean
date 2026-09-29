-- Prove2me | solution 1 for fermat_little_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:58.721898+00:00
-- url     : https://prove2.me/submissions/b434826e-0cd5-45c6-9dbb-3babcf86ea17

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) : (3 : ℤ) ∣ a ^ 3 - a := by
  have key : ∀ x : ZMod 3, x ^ 3 - x = 0 := by decide
  have h : ((a ^ 3 - a : ℤ) : ZMod 3) = 0 := by push_cast; exact key _
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
