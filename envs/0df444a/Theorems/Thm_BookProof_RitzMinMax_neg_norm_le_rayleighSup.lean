-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_neg_norm_le_rayleighSup
-- name    : BookProof.RitzMinMax.neg_norm_le_rayleighSup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:06:52.966804+00:00
-- url     : https://prove2.me/theorems/21ef108f-123f-45bd-a836-b05977e65502
-- title:
--   (T : F →L[ℂ] F) {S : Submodule ℂ F} (hS : 0 < Module.finrank ℂ S) : -‖T‖ ≤ rayleighSup T S
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.neg_norm_le_rayleighSup` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.neg_norm_le_rayleighSup
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.neg_norm_le_rayleighSup (T : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : -‖T‖ ≤ rayleighSup T S := by sorry
