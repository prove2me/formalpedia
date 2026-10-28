-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_bddRealSup_eq_ennrealOfRealSup_toReal
-- name    : AvramDividend.Classical.countable_bddRealSup_eq_ennrealOfRealSup_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:53:12.265275+00:00
-- url     : https://prove2.me/theorems/83c83f86-1396-4148-99fe-31cd0a346355
-- title:
--   Countable real running-record supremum equals its measurable ENNReal encoding
-- statement:
--   For a countable collection of real path observations that is bounded above and has nonnegative supremum, the real supremum is recovered exactly by taking ENNReal.ofReal of each observation, an ENNReal countable supremum and then ENNReal.toReal. This is the order-conversion step needed to identify measurable sampled dividend regulators with their true finite-time running maxima.
-- source:
--   Pinned Mathlib ENNReal.toReal_iSup, ENNReal.toReal_ofReal and ENNReal.ofReal_eq_zero; Avram et al (2007), Proposition 1 sampled-regulator formalisation.

import Mathlib.Data.ENNReal.Operations

open Set
open scoped ENNReal

theorem AvramDividend.Classical.countable_bddRealSup_eq_ennrealOfRealSup_toReal (f : ℕ → ℝ)
    (hb : BddAbove (Set.range f))
    (hzero : 0 ≤ ⨆ i : ℕ, f i) :
    (⨆ i : ℕ, ENNReal.ofReal (f i)).toReal = ⨆ i : ℕ, f i := by
  sorry
