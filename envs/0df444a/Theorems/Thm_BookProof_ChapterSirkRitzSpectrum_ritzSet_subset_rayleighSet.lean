-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzSet_subset_rayleighSet
-- name    : BookProof.ChapterSirkRitzSpectrum.ritzSet_subset_rayleighSet
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:30:12.396152+00:00
-- url     : https://prove2.me/theorems/73a5bd44-a34c-41f9-b773-28e38e97b846
-- title:
--   (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) : ritzSet (finiteModeRestrict A b) (finiteModeDomain b) ⊆ rayleighSet A
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.ritzSet_subset_rayleighSet` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.ritzSet_subset_rayleighSet
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.ritzSet_subset_rayleighSet (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    ritzSet (finiteModeRestrict A b) (finiteModeDomain b) ⊆ rayleighSet A := by sorry
