-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_clmPow
-- name    : BookProof.ChapterSolidHarmonicTools.contDiff_clmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:01.990977+00:00
-- url     : https://prove2.me/theorems/e6e4db49-3234-425d-bb44-a7baba5b8c31
-- title:
--   `BookProof.ChapterSolidHarmonicTools.contDiff_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (ψ y) ^ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.contDiff_clmPow` (ψ : E →L[ℝ] ℂ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (ψ y) ^ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.contDiff_clmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.contDiff_clmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.contDiff_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (ψ y) ^ k := by sorry
