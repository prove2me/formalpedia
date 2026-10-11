-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_rclmPow
-- name    : BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:34.391653+00:00
-- url     : https://prove2.me/theorems/f7f5ff6d-0d2b-4c52-a52a-211f96a7a7d9
-- title:
--   `BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) : (Δ fun y => (L y) ^ k) x = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2) * ∑ i, (L (stdOrthono
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) : (Δ fun y => (L y) ^ k) x = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2) * ∑ i, (L (stdOrthonormalBasis ℝ E i)) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow
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

theorem BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    (Δ fun y => (L y) ^ k) x
      = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2)
          * ∑ i, (L (stdOrthonormalBasis ℝ E i)) ^ 2 := by sorry
