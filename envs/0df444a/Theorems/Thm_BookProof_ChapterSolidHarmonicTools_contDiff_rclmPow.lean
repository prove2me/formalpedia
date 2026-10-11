-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_rclmPow
-- name    : BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:46.879721+00:00
-- url     : https://prove2.me/theorems/28efad84-1a0b-4ec0-b199-9abb6c879752
-- title:
--   `BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (L y) ^ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (L y) ^ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (L y) ^ k := by sorry
