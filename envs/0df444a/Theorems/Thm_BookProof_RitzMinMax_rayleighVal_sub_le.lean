-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighVal_sub_le
-- name    : BookProof.RitzMinMax.rayleighVal_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:29:49.704934+00:00
-- url     : https://prove2.me/theorems/846f2c11-cee8-487e-afe9-515a9606cf15
-- title:
--   (T : F →L[ℂ] F) (y u : F) : rayleighVal T y - rayleighVal T u ≤ ‖T‖ * (‖y‖ + ‖u‖) * ‖y - u‖
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighVal_sub_le` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighVal_sub_le
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighVal_sub_le (T : F →L[ℂ] F) (y u : F) :
    rayleighVal T y - rayleighVal T u ≤ ‖T‖ * (‖y‖ + ‖u‖) * ‖y - u‖ := by sorry
