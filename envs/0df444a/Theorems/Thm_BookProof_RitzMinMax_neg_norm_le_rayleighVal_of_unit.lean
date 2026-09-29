-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_neg_norm_le_rayleighVal_of_unit
-- name    : BookProof.RitzMinMax.neg_norm_le_rayleighVal_of_unit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:49:56.422105+00:00
-- url     : https://prove2.me/theorems/33e2ab5a-9e85-4b76-8a93-ec1f148a29dd
-- title:
--   (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) : -‖T‖ ≤ rayleighVal T x
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.neg_norm_le_rayleighVal_of_unit` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.neg_norm_le_rayleighVal_of_unit
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.neg_norm_le_rayleighVal_of_unit (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    -‖T‖ ≤ rayleighVal T x := by sorry
