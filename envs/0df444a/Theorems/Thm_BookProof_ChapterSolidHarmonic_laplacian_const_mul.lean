-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_laplacian_const_mul
-- name    : BookProof.ChapterSolidHarmonic.laplacian_const_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:53:24.177114+00:00
-- url     : https://prove2.me/theorems/05ddbead-8cbb-4e19-9caf-14275e63df58
-- title:
--   `BookProof.ChapterSolidHarmonic.laplacian_const_mul` {f : E → ℝ} {x : E} (c : ℝ) (hf : ContDiffAt ℝ 2 f x) : (Δ fun y => c * f y) x = c * (Δ f) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.laplacian_const_mul` {f : E → ℝ} {x : E} (c : ℝ) (hf : ContDiffAt ℝ 2 f x) : (Δ fun y => c * f y) x = c * (Δ f) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.laplacian_const_mul`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.laplacian_const_mul
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonic.laplacian_const_mul {f : E → ℝ} {x : E} (c : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    (Δ fun y => c * f y) x = c * (Δ f) x := by sorry
