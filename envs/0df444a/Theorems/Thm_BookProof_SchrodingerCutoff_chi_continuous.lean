-- Prove2me | Theorems.Thm_BookProof_SchrodingerCutoff_chi_continuous
-- name    : BookProof.SchrodingerCutoff.chi_continuous
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:32:25.290258+00:00
-- url     : https://prove2.me/theorems/76ade372-61c7-4302-9c6c-a11f30116dcf
-- title:
--   The Lean 4 theorem `chi_continuous` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `chi_continuous` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchrodingerCutoffEsa.lean

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.chi_continuous
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterParityChirality
open BookProof.ChapterParityChirality
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem BookProof.SchrodingerCutoff.chi_continuous : Continuous chi := by sorry
