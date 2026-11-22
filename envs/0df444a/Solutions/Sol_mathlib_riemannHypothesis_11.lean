-- Prove2me | solution 11 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:01.965043+00:00
-- url     : https://prove2.me/submissions/0f91058a-886e-4d2b-8d84-96f57cfd3a42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_moebius_summatory_rpow_bound
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

theorem solution : RiemannHypothesis :=
  by
  intro s hz htriv hone
  have key : ∀ ε : ℝ, 0 < ε → 1 / 2 - ε ≤ s.re ∧ s.re ≤ 1 / 2 + ε := by
    intro ε hε
    have h := nontrivial_zero_strip_of_moebius_summatory_power_bound
      (r := 1 / 2 + ε) (by linarith) (moebius_summatory_rpow_bound ε hε) hz htriv hone
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
