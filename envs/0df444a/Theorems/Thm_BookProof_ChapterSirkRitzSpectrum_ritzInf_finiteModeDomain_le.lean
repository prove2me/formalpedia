-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzInf_finiteModeDomain_le
-- name    : BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:48:48.078067+00:00
-- url     : https://prove2.me/theorems/c860979a-b16b-46b3-bd09-af1be31dc4b2
-- title:
--   (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {x : F} (hx1 : ‖x‖ = 1) : ritzInf (finiteModeRestrict A b) (finiteModeDomain b) ≤ (inner ℂ x (A x) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_le` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_le
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_le (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    {x : F} (hx1 : ‖x‖ = 1) :
    ritzInf (finiteModeRestrict A b) (finiteModeDomain b) ≤ (inner ℂ x (A x) : ℂ).re := by sorry
