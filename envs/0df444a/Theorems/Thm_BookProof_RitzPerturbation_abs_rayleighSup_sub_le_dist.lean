-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_abs_rayleighSup_sub_le_dist
-- name    : BookProof.RitzPerturbation.abs_rayleighSup_sub_le_dist
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:02:29.58557+00:00
-- url     : https://prove2.me/theorems/5ab7f212-baf1-4238-b119-0d908910c7b1
-- title:
--   (T T' : F →L[ℂ] F) {S : Submodule ℂ F} (hS : 0 < Module.finrank ℂ S) : |rayleighSup T S - rayleighSup T' S| ≤ ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.abs_rayleighSup_sub_le_dist` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.abs_rayleighSup_sub_le_dist
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.abs_rayleighSup_sub_le_dist (T T' : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) :
    |rayleighSup T S - rayleighSup T' S| ≤ ‖T - T'‖ := by sorry
