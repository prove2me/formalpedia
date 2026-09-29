-- Prove2me | Theorems.Thm_BookProof_ChapterH1_phi_one
-- name    : BookProof.ChapterH1.phi_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:43:37.893431+00:00
-- url     : https://prove2.me/theorems/1887bd4a-f5b2-4fb0-9a98-7f4bf878bad6
-- title:
--   {z : ℂ} (hz : z ≠ 0) : phi 1 z = (Complex.exp z - 1) / z
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.phi_one` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.phi_one
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section

theorem BookProof.ChapterH1.phi_one {z : ℂ} (hz : z ≠ 0) : phi 1 z = (Complex.exp z - 1) / z := by sorry
