-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_abs_rayleighVal_le
-- name    : BookProof.RitzMinMax.abs_rayleighVal_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:25:20.128591+00:00
-- url     : https://prove2.me/theorems/3a8e969f-05e1-4ed1-b6ef-411c402b728b
-- title:
--   (T : F →L[ℂ] F) (x : F) : |rayleighVal T x| ≤ ‖T‖ * ‖x‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.abs_rayleighVal_le` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.abs_rayleighVal_le
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.abs_rayleighVal_le (T : F →L[ℂ] F) (x : F) : |rayleighVal T x| ≤ ‖T‖ * ‖x‖ ^ 2 := by sorry
