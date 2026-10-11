-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_hasFDerivAt_rclmPow
-- name    : BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:34.353057+00:00
-- url     : https://prove2.me/theorems/fc6170d9-86f6-45f2-babc-e750e1f9cf16
-- title:
--   `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) : HasFDerivAt (fun y => (L y) ^ k) (((k : ℝ) * (L x) ^ (k - 1)) • (L : E →L[ℝ] ℝ)) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow` (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) : HasFDerivAt (fun y => (L y) ^ k) (((k : ℝ) * (L x) ^ (k - 1)) • (L : E →L[ℝ] ℝ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    HasFDerivAt (fun y => (L y) ^ k) (((k : ℝ) * (L x) ^ (k - 1)) • (L : E →L[ℝ] ℝ)) x := by sorry
