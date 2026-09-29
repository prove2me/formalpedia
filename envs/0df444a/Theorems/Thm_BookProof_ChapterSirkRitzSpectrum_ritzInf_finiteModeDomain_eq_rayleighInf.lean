-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzInf_finiteModeDomain_eq_rayleighInf
-- name    : BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:49:25.099988+00:00
-- url     : https://prove2.me/theorems/0082abc5-0b8b-4efa-b470-f06654299a4e
-- title:
--   [Nontrivial F] (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) : ritzInf (finiteModeRestrict A b) (finiteModeDomain b) = rayleighInf A
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf [Nontrivial F] (A : F →L[ℂ] F)
    (b : HilbertBasis ℕ ℂ F) :
    ritzInf (finiteModeRestrict A b) (finiteModeDomain b) = rayleighInf A := by sorry
