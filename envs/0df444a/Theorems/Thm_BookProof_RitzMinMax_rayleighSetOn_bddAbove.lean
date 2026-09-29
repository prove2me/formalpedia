-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_rayleighSetOn_bddAbove
-- name    : BookProof.RitzMinMax.rayleighSetOn_bddAbove
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:59:15.078752+00:00
-- url     : https://prove2.me/theorems/537c06fc-0f24-4542-bc78-39a2cb8b78b8
-- title:
--   (T : F →L[ℂ] F) (S : Submodule ℂ F) : BddAbove (rayleighSetOn T S)
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.rayleighSetOn_bddAbove` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.rayleighSetOn_bddAbove
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.rayleighSetOn_bddAbove (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    BddAbove (rayleighSetOn T S) := by sorry
