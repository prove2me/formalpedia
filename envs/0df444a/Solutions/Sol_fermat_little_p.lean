-- Prove2me | solution 1 for fermat_little_p
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:36:16.952483+00:00
-- url     : https://prove2.me/submissions/6b309c58-8f1e-49d7-8380-a1e03f9bb5c6

import Mathlib.Data.Int.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (p : ℕ) (hp : p.Prime) (a : ℤ) : (p : ℤ) ∣ a ^ p - a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : ((a ^ p - a : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
