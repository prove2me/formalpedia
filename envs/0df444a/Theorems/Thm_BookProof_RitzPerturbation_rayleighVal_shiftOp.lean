-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_rayleighVal_shiftOp
-- name    : BookProof.RitzPerturbation.rayleighVal_shiftOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:34:21.689166+00:00
-- url     : https://prove2.me/theorems/76ccfaf4-ebc3-44e4-996b-ee2e961353ae
-- title:
--   (T : F →L[ℂ] F) (c : ℝ) {x : F} (hx1 : ‖x‖ = 1) : rayleighVal (shiftOp T c) x = rayleighVal T x + c
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.rayleighVal_shiftOp` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.rayleighVal_shiftOp
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.rayleighVal_shiftOp (T : F →L[ℂ] F) (c : ℝ) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighVal (shiftOp T c) x = rayleighVal T x + c := by sorry
