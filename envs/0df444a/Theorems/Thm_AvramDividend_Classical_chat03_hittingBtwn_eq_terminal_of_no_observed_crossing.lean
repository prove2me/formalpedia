-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
-- name    : AvramDividend.Classical.chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:51:30.186346+00:00
-- url     : https://prove2.me/theorems/42afa059-764f-47cf-a2dc-0e999983bb09
-- title:
--   Bounded first-hit index equals its terminal cap when no earlier observation hits
-- statement:
--   For an arbitrary observed sequence and set of hit values, the Mathlib bounded hittingBtwn index with initial index zero and terminal cap m equals m whenever no sampled index strictly below m belongs to the hit set. The lemma prepares the strict two-sided Lévy non-exit case of the capped grid-to-continuous limit.
-- source:
--   Pinned Mathlib hittingBtwn_le and hittingBtwn_lt_iff, via contrapositive of the existence of an earlier hit.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
    {Ω β : Type*} [MeasurableSpace Ω]
    (u : ℕ → Ω → β) (s : Set β) (ω : Ω)
    (m : ℕ) (hnone : ∀ j : ℕ, j < m → u j ω ∉ s) :
    hittingBtwn u s 0 m ω = m := by sorry
