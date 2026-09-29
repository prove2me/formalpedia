-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_one_lt_ratio
-- name    : BookProof.SirkGapTable.one_lt_ratio
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:42:53.964313+00:00
-- url     : https://prove2.me/theorems/04b3e791-5ddb-435f-8674-87312d91ec03
-- title:
--   {l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) : 1 < (l2 / l1) ^ p
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.one_lt_ratio` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.one_lt_ratio
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

theorem BookProof.SirkGapTable.one_lt_ratio {l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    1 < (l2 / l1) ^ p := by sorry
