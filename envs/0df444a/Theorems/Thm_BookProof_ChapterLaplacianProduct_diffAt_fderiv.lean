-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_diffAt_fderiv
-- name    : BookProof.ChapterLaplacianProduct.diffAt_fderiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:22:10.119983+00:00
-- url     : https://prove2.me/theorems/a3d78b1a-f52d-468e-9eb3-fbc7db86c4c0
-- title:
--   `BookProof.ChapterLaplacianProduct.diffAt_fderiv` {f : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.diffAt_fderiv` {f : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.diffAt_fderiv`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.diffAt_fderiv
import Definitions.Def_ChapterRadialLaplacian
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.diffAt_fderiv {f : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fderiv ℝ f) x := by sorry
