-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_fderiv_radial
-- name    : BookProof.ChapterLaplacianProduct.fderiv_radial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:23:09.67198+00:00
-- url     : https://prove2.me/theorems/9b933858-de56-4dcf-a18b-889044a0cd50
-- title:
--   `BookProof.ChapterLaplacianProduct.fderiv_radial` {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) : fderiv ℝ (fun y : E => g ‖y‖) x = (deriv g ‖x‖ /...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.fderiv_radial` {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) : fderiv ℝ (fun y : E => g ‖y‖) x = (deriv g ‖x‖ / ‖x‖) • innerCLM E x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.fderiv_radial`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.fderiv_radial
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.fderiv_radial {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) :
    fderiv ℝ (fun y : E => g ‖y‖) x = (deriv g ‖x‖ / ‖x‖) • innerCLM E x := by sorry
