-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighSup_span_singleton
-- name    : BookProof.RitzMinMax.rayleighSup_span_singleton
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:01:00.784528+00:00
-- url     : https://prove2.me/theorems/9709f23d-8d51-47e5-8026-bfab921e7b2b
-- title:
--   (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) : rayleighSup T (Submodule.span ℂ {x}) = rayleighVal T x
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighSup_span_singleton` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighSup_span_singleton
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighSup_span_singleton (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighSup T (Submodule.span ℂ {x}) = rayleighVal T x := by sorry
