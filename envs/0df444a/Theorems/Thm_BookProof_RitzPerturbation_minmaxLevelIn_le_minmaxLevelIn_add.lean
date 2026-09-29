-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxLevelIn_le_minmaxLevelIn_add
-- name    : BookProof.RitzPerturbation.minmaxLevelIn_le_minmaxLevelIn_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:03:14.752263+00:00
-- url     : https://prove2.me/theorems/ad8b88ee-4181-4180-bf83-81b7ade3d3da
-- title:
--   (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) (hne : (minmaxSetIn T' W k).Nonempty) : minmaxLevelIn T W k ≤ minmaxLevelIn T' W k + ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxLevelIn_le_minmaxLevelIn_add` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxLevelIn_le_minmaxLevelIn_add
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxLevelIn_le_minmaxLevelIn_add (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T' W k).Nonempty) :
    minmaxLevelIn T W k ≤ minmaxLevelIn T' W k + ‖T - T'‖ := by sorry
