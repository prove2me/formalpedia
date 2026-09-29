-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_finrank_galerkinSpan
-- name    : BookProof.RitzMinMax.finrank_galerkinSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:28:09.793656+00:00
-- url     : https://prove2.me/theorems/d009dc2b-3ab0-453f-84a3-87096eadc072
-- title:
--   (b : HilbertBasis ℕ ℂ F) (m : ℕ) : Module.finrank ℂ (galerkinSpan b m) = m
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.finrank_galerkinSpan` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.finrank_galerkinSpan
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.finrank_galerkinSpan (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    Module.finrank ℂ (galerkinSpan b m) = m := by sorry
