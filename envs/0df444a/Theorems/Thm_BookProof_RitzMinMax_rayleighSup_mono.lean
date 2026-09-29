-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighSup_mono
-- name    : BookProof.RitzMinMax.rayleighSup_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:07:32.648598+00:00
-- url     : https://prove2.me/theorems/fa3d0bc1-d7a6-4f60-9d81-b042b844a414
-- title:
--   (T : F →L[ℂ] F) {S S' : Submodule ℂ F} (h : S ≤ S') (hS : 0 < Module.finrank ℂ S) : rayleighSup T S ≤ rayleighSup T S'
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighSup_mono` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighSup_mono
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighSup_mono (T : F →L[ℂ] F) {S S' : Submodule ℂ F} (h : S ≤ S')
    (hS : 0 < Module.finrank ℂ S) : rayleighSup T S ≤ rayleighSup T S' := by sorry
