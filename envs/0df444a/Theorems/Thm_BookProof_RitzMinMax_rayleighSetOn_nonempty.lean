-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighSetOn_nonempty
-- name    : BookProof.RitzMinMax.rayleighSetOn_nonempty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:51:09.282838+00:00
-- url     : https://prove2.me/theorems/4cf0b1c4-7212-4f01-ac30-6e88dd021e58
-- title:
--   (T : F →L[ℂ] F) {S : Submodule ℂ F} (hS : 0 < Module.finrank ℂ S) : (rayleighSetOn T S).Nonempty
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighSetOn_nonempty` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighSetOn_nonempty
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighSetOn_nonempty (T : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : (rayleighSetOn T S).Nonempty := by sorry
