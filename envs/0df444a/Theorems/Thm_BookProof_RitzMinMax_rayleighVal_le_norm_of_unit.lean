-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighVal_le_norm_of_unit
-- name    : BookProof.RitzMinMax.rayleighVal_le_norm_of_unit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:50:33.925403+00:00
-- url     : https://prove2.me/theorems/c62fd8d7-a8b1-494f-bc8e-266240868842
-- title:
--   (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) : rayleighVal T x ≤ ‖T‖
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighVal_le_norm_of_unit` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighVal_le_norm_of_unit
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighVal_le_norm_of_unit (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighVal T x ≤ ‖T‖ := by sorry
