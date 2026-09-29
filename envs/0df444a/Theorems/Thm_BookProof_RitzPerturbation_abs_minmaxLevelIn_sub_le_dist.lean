-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_abs_minmaxLevelIn_sub_le_dist
-- name    : BookProof.RitzPerturbation.abs_minmaxLevelIn_sub_le_dist
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:10:17.190446+00:00
-- url     : https://prove2.me/theorems/203fc2c8-c95e-4aa1-85c7-fb7d0e98dd86
-- title:
--   (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) (hne : (minmaxSetIn T W k).Nonempty) : |minmaxLevelIn T W k - minmaxLevelIn T' W k| ≤ ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.abs_minmaxLevelIn_sub_le_dist` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.abs_minmaxLevelIn_sub_le_dist
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.abs_minmaxLevelIn_sub_le_dist (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T W k).Nonempty) :
    |minmaxLevelIn T W k - minmaxLevelIn T' W k| ≤ ‖T - T'‖ := by sorry
