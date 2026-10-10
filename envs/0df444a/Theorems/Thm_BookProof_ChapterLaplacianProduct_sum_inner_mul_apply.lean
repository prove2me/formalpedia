-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_sum_inner_mul_apply
-- name    : BookProof.ChapterLaplacianProduct.sum_inner_mul_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:22:44.072298+00:00
-- url     : https://prove2.me/theorems/f22682db-7e0e-4a75-b119-e7b896094718
-- title:
--   `BookProof.ChapterLaplacianProduct.sum_inner_mul_apply` [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) (x : E) : ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫ * L ((stdOrthonormalBasis ℝ E) i) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.sum_inner_mul_apply` [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) (x : E) : ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫ * L ((stdOrthonormalBasis ℝ E) i) = L x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.sum_inner_mul_apply`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.sum_inner_mul_apply
import Definitions.Def_ChapterRadialLaplacian
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.sum_inner_mul_apply [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) (x : E) :
    ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫ * L ((stdOrthonormalBasis ℝ E) i) = L x := by sorry
