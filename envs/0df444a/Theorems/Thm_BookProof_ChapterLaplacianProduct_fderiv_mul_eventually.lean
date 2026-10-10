-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_fderiv_mul_eventually
-- name    : BookProof.ChapterLaplacianProduct.fderiv_mul_eventually
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:22:27.839984+00:00
-- url     : https://prove2.me/theorems/e006a9d1-913f-4eef-aa02-8195a2b461bb
-- title:
--   `BookProof.ChapterLaplacianProduct.fderiv_mul_eventually` {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) : (fderiv ℝ fun y : E => f y * g y) =ᶠ[nhds x] f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.fderiv_mul_eventually` {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) : (fderiv ℝ fun y : E => f y * g y) =ᶠ[nhds x] fun y => g y • fderiv ℝ f y + f y • fderiv ℝ g y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.fderiv_mul_eventually`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.fderiv_mul_eventually
import Definitions.Def_ChapterRadialLaplacian
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.fderiv_mul_eventually {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (fderiv ℝ fun y : E => f y * g y) =ᶠ[nhds x]
      fun y => g y • fderiv ℝ f y + f y • fderiv ℝ g y := by sorry
