-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_richardson_exact
-- name    : BookProof.SirkGapTable.richardson_exact
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:44:41.267509+00:00
-- url     : https://prove2.me/theorems/b19524ba-a43b-4bee-bac8-42eff1c33a81
-- title:
--   {D C l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) : richardson (D + C * l1 ^ (-p)) (D + C * l2 ^ (-p)) l1 l2 p = D
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.richardson_exact` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.richardson_exact
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

theorem BookProof.SirkGapTable.richardson_exact {D C l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    richardson (D + C * l1 ^ (-p)) (D + C * l2 ^ (-p)) l1 l2 p = D := by sorry
