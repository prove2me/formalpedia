-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_minmaxSetIn_nonempty_congr
-- name    : BookProof.RitzPerturbation.minmaxSetIn_nonempty_congr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:32:23.578801+00:00
-- url     : https://prove2.me/theorems/eecf45d1-b9b2-4459-b071-5d5b83681a8d
-- title:
--   (T T' : F →L[ℂ] F) {W : Submodule ℂ F} {k : ℕ} (h : (minmaxSetIn T W k).Nonempty) : (minmaxSetIn T' W k).Nonempty
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.minmaxSetIn_nonempty_congr` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxSetIn_nonempty_congr
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.minmaxSetIn_nonempty_congr (T T' : F →L[ℂ] F) {W : Submodule ℂ F} {k : ℕ}
    (h : (minmaxSetIn T W k).Nonempty) : (minmaxSetIn T' W k).Nonempty := by sorry
