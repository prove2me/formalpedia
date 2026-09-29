-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxLevel_le_minmaxLevelIn_add
-- name    : BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevelIn_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:11:01.491231+00:00
-- url     : https://prove2.me/theorems/b684ae15-21d6-4fca-ae13-98e79832bed7
-- title:
--   (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) (hne : (minmaxSetIn T' W k).Nonempty) : minmaxLevel T k ≤ minmaxLevelIn T' W k + ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevelIn_add` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevelIn_add
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevelIn_add (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T' W k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevelIn T' W k + ‖T - T'‖ := by sorry
