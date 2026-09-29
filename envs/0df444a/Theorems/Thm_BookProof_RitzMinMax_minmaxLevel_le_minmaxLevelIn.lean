-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxLevel_le_minmaxLevelIn
-- name    : BookProof.RitzMinMax.minmaxLevel_le_minmaxLevelIn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:20:15.857022+00:00
-- url     : https://prove2.me/theorems/4bdae9b5-6d98-4931-887c-de9ecc426bff
-- title:
--   (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) (hne : (minmaxSetIn T W k).Nonempty) : minmaxLevel T k ≤ minmaxLevelIn T W k
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxLevel_le_minmaxLevelIn` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxLevel_le_minmaxLevelIn
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxLevel_le_minmaxLevelIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T W k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevelIn T W k := by sorry
