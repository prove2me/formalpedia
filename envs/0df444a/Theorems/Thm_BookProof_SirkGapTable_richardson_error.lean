-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_richardson_error
-- name    : BookProof.SirkGapTable.richardson_error
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:32:51.44924+00:00
-- url     : https://prove2.me/theorems/5a68c0a7-adc8-4fa9-a43e-8defb9b4b9f0
-- title:
--   {D C l1 l2 p d1 d2 eps : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) (h1 : |d1 - (D + C * l1 ^ (-p))| ≤ eps) (h2 : |d2 - (D + C * l2 ^ (-p))| ≤ eps) : |richardson d1 d2 l1 l2 p - D| ≤ eps * (1...
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.richardson_error` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.richardson_error
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

theorem BookProof.SirkGapTable.richardson_error {D C l1 l2 p d1 d2 eps : ℝ}
    (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p)
    (h1 : |d1 - (D + C * l1 ^ (-p))| ≤ eps) (h2 : |d2 - (D + C * l2 ^ (-p))| ≤ eps) :
    |richardson d1 d2 l1 l2 p - D| ≤ eps * (1 + 2 / ((l2 / l1) ^ p - 1)) := by sorry
