-- Prove2me | Theorems.Thm_BookProof_ChapterH6_sirk_error_bound_antitone
-- name    : BookProof.ChapterH6.sirk_error_bound_antitone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-22T03:42:24.87025+00:00
-- url     : https://prove2.me/theorems/8cc655a1-efbe-456c-926d-29076f8e6ed7
-- title:
--   The Lean 4 theorem `sirk_error_bound_antitone` in the `ChapterH6` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_error_bound_antitone` in the `ChapterH6` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.sirk_error_bound_antitone
import Mathlib
import Definitions.Def_ChapterH6
open BookProof.ChapterH6


noncomputable section

open Filter Topology

theorem BookProof.ChapterH6.sirk_error_bound_antitone (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) :
    Antitone (fun m : ℕ => sirkBound C Dmin h nv m) := by sorry
