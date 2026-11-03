-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
-- name    : AvramDividend.Classical.avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:35:21.553838+00:00
-- url     : https://prove2.me/theorems/3cb3ca42-04d5-4cfe-b005-72610a0291ab
-- title:
--   Every strict negative càdlàg path jump has a separating rational level and two local time neighbourhoods
-- statement:
--   For an arbitrary real càdlàg path and any strictly downward jump at positive time t, if the left-limit and right-continuity filters converge, there exists a rational threshold a and open-left/closed-right time neighbourhoods with all left values above a and all right values below a. This is the deterministic geometric ingredient needed to enumerate exact source jumps using measurable countable rational grid first hitting times, with no auxiliary probability process.
-- source:
--   Abstract the Proved source-exact rational separation theorem 2ec22b22 from the actual X to a generic path with explicitly stated convergence assumptions; use exists_rat_btwn and Mathlib neighbourhood filter eventually-to-interval lemmas.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_path_strict_downjump_rational_neighbourhood_separation
    (Y : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hdown : Y t < Function.leftLim Y t)
    (hLeft : Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hRight : ContinuousWithinAt Y (Ici t) t) :
    ∃ (a : ℚ) (s b : ℝ≥0), s < t ∧ t < b ∧
      (∀ u ∈ Ioo s t, (a : ℝ) < Y u) ∧
      (∀ u ∈ Ico t b, Y u < (a : ℝ)) := by sorry
