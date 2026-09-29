-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighVal_smul
-- name    : BookProof.RitzMinMax.rayleighVal_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:29:12.337361+00:00
-- url     : https://prove2.me/theorems/f3b25a7c-6d22-4bd5-a6e1-8a28163f7961
-- title:
--   (T : F →L[ℂ] F) (c : ℂ) (x : F) : rayleighVal T (c • x) = ‖c‖ ^ 2 * rayleighVal T x
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighVal_smul` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighVal_smul
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighVal_smul (T : F →L[ℂ] F) (c : ℂ) (x : F) :
    rayleighVal T (c • x) = ‖c‖ ^ 2 * rayleighVal T x := by sorry
