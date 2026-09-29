-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxSet_bddBelow
-- name    : BookProof.RitzMinMax.minmaxSet_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:14:36.43723+00:00
-- url     : https://prove2.me/theorems/6db97372-4a2a-4eb4-b346-3b2f4e532479
-- title:
--   (T : F →L[ℂ] F) (k : ℕ) : BddBelow (minmaxSet T k)
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxSet_bddBelow` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxSet_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxSet_bddBelow (T : F →L[ℂ] F) (k : ℕ) : BddBelow (minmaxSet T k) := by sorry
