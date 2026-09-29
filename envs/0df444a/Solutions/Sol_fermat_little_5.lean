-- Prove2me | solution 1 for fermat_little_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:18:39.878861+00:00
-- url     : https://prove2.me/submissions/0227146a-64bc-4c4b-8ed1-f131efd1b87c

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (a : ℤ) : (5 : ℤ) ∣ a ^ 5 - a := by
  have key : ∀ x : ZMod 5, x ^ 5 - x = 0 := by decide
  have h : ((a ^ 5 - a : ℤ) : ZMod 5) = 0 := by
    push_cast
    exact key _
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
