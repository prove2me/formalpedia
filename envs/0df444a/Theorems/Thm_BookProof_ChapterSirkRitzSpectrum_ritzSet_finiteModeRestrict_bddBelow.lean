-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzSet_finiteModeRestrict_bddBelow
-- name    : BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:47:31.296083+00:00
-- url     : https://prove2.me/theorems/74dd738b-21cf-4ab8-b454-bcb9297bacfc
-- title:
--   (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) : BddBelow (ritzSet (finiteModeRestrict A b) (finiteModeDomain b))
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_bddBelow` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_bddBelow (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    BddBelow (ritzSet (finiteModeRestrict A b) (finiteModeDomain b)) := by sorry
