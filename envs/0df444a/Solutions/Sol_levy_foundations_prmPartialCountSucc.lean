-- Prove2me | solution 1 for levy_foundations_prmPartialCountSucc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:13:21.978899+00:00
-- url     : https://prove2.me/submissions/0876360d-09f6-4f7d-925e-cc768a71deb4

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_prmPartialCount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (A : Set E)
    (n : ℕ) (ω : Ω) :
    LevyFoundations.prmPartialCount K X A (n + 1) ω =
      LevyFoundations.prmPartialCount K X A n ω +
        LevyFoundations.thinnedCount K X A (n + 1) ω := by
  unfold LevyFoundations.prmPartialCount
  rw [Finset.sum_range_succ]
