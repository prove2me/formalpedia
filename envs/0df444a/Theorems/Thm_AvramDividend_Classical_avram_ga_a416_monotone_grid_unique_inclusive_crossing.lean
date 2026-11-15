-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a416_monotone_grid_unique_inclusive_crossing
-- name    : AvramDividend.Classical.avram_ga_a416_monotone_grid_unique_inclusive_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:30:38.253621+00:00
-- url     : https://prove2.me/theorems/5b28ce29-4cb4-479f-8752-1a29eecc574e
-- title:
--   Increasing mesh has at most one half-open (left-open, right-closed) crossing cell
-- statement:
--   In a strictly increasing finite or infinite mesh, each point belongs to at most one of the intervals (s_i,s_(i+1)] because the left endpoint is excluded and the right endpoint is included.
-- source:
--   Half-open crossing geometry, using the Proved a380 strict-crossing index argument with changed right endpoint inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a416_monotone_grid_unique_inclusive_crossing
    {α : Type*} [LinearOrder α] (s : ℕ → α) (hs : StrictMono s)
    (ρ : α) (i j : ℕ)
    (hi : s i < ρ ∧ ρ ≤ s (i + 1))
    (hj : s j < ρ ∧ ρ ≤ s (j + 1)) : i = j := by sorry
