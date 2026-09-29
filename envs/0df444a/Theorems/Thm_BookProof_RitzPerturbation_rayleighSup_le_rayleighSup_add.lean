-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_rayleighSup_le_rayleighSup_add
-- name    : BookProof.RitzPerturbation.rayleighSup_le_rayleighSup_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:54:02.612327+00:00
-- url     : https://prove2.me/theorems/a25c033b-eda8-4b24-9bb5-d215cad18ee3
-- title:
--   (T T' : F →L[ℂ] F) {S : Submodule ℂ F} (hS : 0 < Module.finrank ℂ S) : rayleighSup T S ≤ rayleighSup T' S + ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.rayleighSup_le_rayleighSup_add` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.rayleighSup_le_rayleighSup_add
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.rayleighSup_le_rayleighSup_add (T T' : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) :
    rayleighSup T S ≤ rayleighSup T' S + ‖T - T'‖ := by sorry
