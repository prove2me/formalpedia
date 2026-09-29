-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighVal_le_rayleighSup
-- name    : BookProof.RitzMinMax.rayleighVal_le_rayleighSup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:08:08.402986+00:00
-- url     : https://prove2.me/theorems/6e643f9c-5902-4f19-8359-9c713841d9c4
-- title:
--   (T : F →L[ℂ] F) {S : Submodule ℂ F} {x : F} (hx : x ∈ S) (hx1 : ‖x‖ = 1) : rayleighVal T x ≤ rayleighSup T S
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighVal_le_rayleighSup` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighVal_le_rayleighSup
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighVal_le_rayleighSup (T : F →L[ℂ] F) {S : Submodule ℂ F} {x : F}
    (hx : x ∈ S) (hx1 : ‖x‖ = 1) : rayleighVal T x ≤ rayleighSup T S := by sorry
