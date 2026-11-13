-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a32_compact_translation_vanishing_radius
-- name    : AvramDividend.Classical.avram_ga_a32_compact_translation_vanishing_radius
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:26:42.365125+00:00
-- url     : https://prove2.me/theorems/11fe368b-a6af-41f3-bfdc-42e601e17031
-- title:
--   Moving compact base with arbitrarily small interior margin is stable under vanishing shifts
-- statement:
--   For continuous w on the compact interval enlarged by any positive margin r, moving points in the smaller interval and additive displacements tending to zero yield value increments tending to zero. This handles positive compact reserve bands with arbitrarily small lower floor, exactly as needed for the final clipped original Gaussian cell on the horizon-boundary event.
-- source:
--   Root-connected terminal theorem ad246ef2; strong original path increment limit 85dd6f23; compact original rightLimit-D reserve band e7de7c19.

import Mathlib
open Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a32_compact_translation_vanishing_radius
    (w : ℝ → ℝ) (a b r : ℝ) (hr : 0 < r)
    (hw : ContinuousOn w (Set.Icc (a - r) (b + r)))
    (y δ : ℕ → ℝ) (hy : ∀ m, y m ∈ Set.Icc a b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => w (y m + δ m) - w (y m))
      atTop (nhds (0 : ℝ)) := by sorry
