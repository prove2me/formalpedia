-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_minmaxSetIn_subset
-- name    : BookProof.RitzMinMax.minmaxSetIn_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:28:42.129738+00:00
-- url     : https://prove2.me/theorems/f0253d0f-8efb-4e9d-b94b-c59600a02ea8
-- title:
--   (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : minmaxSetIn T W k ⊆ minmaxSet T k
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.minmaxSetIn_subset` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxSetIn_subset
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.minmaxSetIn_subset (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxSetIn T W k ⊆ minmaxSet T k := by sorry
