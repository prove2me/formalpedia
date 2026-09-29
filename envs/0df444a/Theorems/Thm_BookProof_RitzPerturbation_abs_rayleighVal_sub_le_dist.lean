-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_abs_rayleighVal_sub_le_dist
-- name    : BookProof.RitzPerturbation.abs_rayleighVal_sub_le_dist
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:53:30.764136+00:00
-- url     : https://prove2.me/theorems/2c8ed8f2-89d4-4453-a780-917a7b6f05ce
-- title:
--   (T T' : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) : |rayleighVal T x - rayleighVal T' x| ≤ ‖T - T'‖
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.abs_rayleighVal_sub_le_dist` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.abs_rayleighVal_sub_le_dist
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.abs_rayleighVal_sub_le_dist (T T' : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    |rayleighVal T x - rayleighVal T' x| ≤ ‖T - T'‖ := by sorry
