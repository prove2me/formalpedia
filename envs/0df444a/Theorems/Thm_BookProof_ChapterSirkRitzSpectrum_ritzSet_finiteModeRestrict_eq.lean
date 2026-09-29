-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzSet_finiteModeRestrict_eq
-- name    : BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:29:23.377749+00:00
-- url     : https://prove2.me/theorems/7af585c3-defa-488a-a3b7-29d06c003e38
-- title:
--   (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) : ritzSet (finiteModeRestrict A b) (finiteModeDomain b) = {t : ℝ | ∃ u : F, u ∈ finiteModeDomain b ∧ ‖u‖ = 1 ∧ t = (inner ℂ u (A u) : ℂ).re}
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_eq` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_eq
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_eq (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    ritzSet (finiteModeRestrict A b) (finiteModeDomain b) =
      {t : ℝ | ∃ u : F, u ∈ finiteModeDomain b ∧ ‖u‖ = 1 ∧ t = (inner ℂ u (A u) : ℂ).re} := by sorry
