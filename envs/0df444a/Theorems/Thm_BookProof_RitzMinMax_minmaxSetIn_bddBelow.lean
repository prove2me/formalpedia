-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxSetIn_bddBelow
-- name    : BookProof.RitzMinMax.minmaxSetIn_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:13:56.164224+00:00
-- url     : https://prove2.me/theorems/c265c231-be15-468c-9e53-41512dc7fd2a
-- title:
--   (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : BddBelow (minmaxSetIn T W k)
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxSetIn_bddBelow` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxSetIn_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxSetIn_bddBelow (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    BddBelow (minmaxSetIn T W k) := by sorry
