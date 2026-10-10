-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_fderiv_fderiv_mul
-- name    : BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:22:14.035894+00:00
-- url     : https://prove2.me/theorems/f4849f57-23b4-4baa-9a99-da8ab6a5f71b
-- title:
--   `BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul` {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) : fderiv ℝ (fderiv ℝ fun y : E => f y * g y) x = (g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul` {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) : fderiv ℝ (fderiv ℝ fun y : E => f y * g y) x = (g x) • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x) + ((f x) • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul
import Definitions.Def_ChapterRadialLaplacian
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.fderiv_fderiv_mul {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ fun y : E => f y * g y) x
      = (g x) • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)
        + ((f x) • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) := by sorry
