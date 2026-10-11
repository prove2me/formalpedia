-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_normSqPow
-- name    : BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:59.902852+00:00
-- url     : https://prove2.me/theorems/bbc0a912-7c73-4c8f-9397-c4773ac48780
-- title:
--   `BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow` (m : ℕ) : ContDiff ℝ 2 fun y : E => (‖y‖ ^ 2) ^ m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow` (m : ℕ) : ContDiff ℝ 2 fun y : E => (‖y‖ ^ 2) ^ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.contDiff_normSqPow (m : ℕ) : ContDiff ℝ 2 fun y : E => (‖y‖ ^ 2) ^ m := by sorry
