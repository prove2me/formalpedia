-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_rayleighSup_shiftOp
-- name    : BookProof.RitzPerturbation.rayleighSup_shiftOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:52:55.57891+00:00
-- url     : https://prove2.me/theorems/f78de27b-4ae4-4121-953d-8f2ecfe85168
-- title:
--   (T : F →L[ℂ] F) (c : ℝ) {S : Submodule ℂ F} (hS : 0 < Module.finrank ℂ S) : rayleighSup (shiftOp T c) S = rayleighSup T S + c
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.rayleighSup_shiftOp` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.rayleighSup_shiftOp
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.rayleighSup_shiftOp (T : F →L[ℂ] F) (c : ℝ) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) :
    rayleighSup (shiftOp T c) S = rayleighSup T S + c := by sorry
