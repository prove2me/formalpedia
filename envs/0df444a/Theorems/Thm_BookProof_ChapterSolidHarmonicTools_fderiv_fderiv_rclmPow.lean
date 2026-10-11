-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_fderiv_fderiv_rclmPow
-- name    : BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_rclmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:51.365974+00:00
-- url     : https://prove2.me/theorems/c0afa9d3-1608-4ee1-9b26-9e729528783a
-- title:
--   `BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) (x v w : E) : fderiv ℝ (fderiv ℝ fun y => (L y) ^ k) x v w = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) (x v w : E) : fderiv ℝ (fderiv ℝ fun y => (L y) ^ k) x v w = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2) * L v * L w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_rclmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_rclmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.fderiv_fderiv_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) (x v w : E) :
    fderiv ℝ (fderiv ℝ fun y => (L y) ^ k) x v w
      = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2) * L v * L w := by sorry
