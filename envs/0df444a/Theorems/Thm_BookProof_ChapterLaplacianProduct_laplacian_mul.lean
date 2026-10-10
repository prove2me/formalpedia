-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_laplacian_mul
-- name    : BookProof.ChapterLaplacianProduct.laplacian_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:22:24.060983+00:00
-- url     : https://prove2.me/theorems/d28731b5-d2c8-40a9-be8f-a24c9325d7ff
-- title:
--   `BookProof.ChapterLaplacianProduct.laplacian_mul` [FiniteDimensional ℝ E] {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) : (Δ fun y : E => f y * g y) x =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.laplacian_mul` [FiniteDimensional ℝ E] {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) : (Δ fun y : E => f y * g y) x = (Δ f) x * g x + f x * (Δ g) x + 2 * ∑ i, fderiv ℝ f x ((stdOrthonormalBasis ℝ E) i) * fderiv ℝ g x ((stdOrthonormalBasis ℝ E) i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.laplacian_mul`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.laplacian_mul
import Definitions.Def_ChapterRadialLaplacian
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.laplacian_mul [FiniteDimensional ℝ E] {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (Δ fun y : E => f y * g y) x
      = (Δ f) x * g x + f x * (Δ g) x
        + 2 * ∑ i, fderiv ℝ f x ((stdOrthonormalBasis ℝ E) i)
            * fderiv ℝ g x ((stdOrthonormalBasis ℝ E) i) := by sorry
