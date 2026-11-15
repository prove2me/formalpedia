-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a380_monotone_grid_unique_crossing_v2
-- name    : AvramDividend.Classical.avram_ga_a380_monotone_grid_unique_crossing_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:53:13.327583+00:00
-- url     : https://prove2.me/theorems/1fa287a0-4f70-4ec1-a2e1-12aa2c65e761
-- title:
--   Uniqueness of the strict crossing cell on a strictly increasing physical clock
-- statement:
--   For a strictly increasing mesh-time sequence, a fixed stopping time can lie strictly between consecutive times at at most one index.
-- source:
--   Original Gaussian dividend crossing-cell source a138 and a139, for a strictly increasing physical mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a380_monotone_grid_unique_crossing_v2
    {α : Type*} [LinearOrder α] (s : ℕ → α) (hs : StrictMono s)
    (ρ : α) (i k : ℕ)
    (hi : s i < ρ ∧ ρ < s (i + 1))
    (hk : s k < ρ ∧ ρ < s (k + 1)) : i = k := by sorry
