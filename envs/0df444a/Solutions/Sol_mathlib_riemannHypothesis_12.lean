-- Prove2me | solution 12 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:03.11392+00:00
-- url     : https://prove2.me/submissions/f596d8d1-9c78-4d72-80ee-10ce0c32836e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_BroughanRH_moebius
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

theorem solution : RiemannHypothesis :=
  by
  intro s hz htriv hone
  have key : ∀ ε : ℝ, 0 < ε → 1 / 2 - ε ≤ s.re ∧ s.re ≤ 1 / 2 + ε := by
    intro ε hε
    have h := nontrivial_zero_strip_of_moebius_summatory_power_bound
      (r := 1 / 2 + ε) (by linarith) (BroughanRH.moebius ε hε) hz htriv hone
    constructor <;> linarith [h.1, h.2]
  have hle : s.re ≤ 1 / 2 := by
    by_contra hlt
    push_neg at hlt
    have := (key ((s.re - 1 / 2) / 2) (by linarith)).2
    linarith
  have hge : 1 / 2 ≤ s.re := by
    by_contra hlt
    push_neg at hlt
    have := (key ((1 / 2 - s.re) / 2) (by linarith)).1
    linarith
  exact le_antisymm hle hge
