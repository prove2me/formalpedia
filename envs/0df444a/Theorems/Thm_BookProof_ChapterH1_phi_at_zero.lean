-- Prove2me | Theorems.Thm_BookProof_ChapterH1_phi_at_zero
-- name    : BookProof.ChapterH1.phi_at_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:15:50.728769+00:00
-- url     : https://prove2.me/theorems/f201767c-5d8c-4ce4-8d07-db457ebdee95
-- title:
--   (k : ℕ) : phi k 0 = 1 / k.factorial
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.phi_at_zero` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.phi_at_zero
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section

theorem BookProof.ChapterH1.phi_at_zero (k : ℕ) : phi k 0 = 1 / k.factorial := by sorry
