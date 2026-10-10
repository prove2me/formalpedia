-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_fderiv_fderiv_comp_normSq
-- name    : BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:58:48.611996+00:00
-- url     : https://prove2.me/theorems/5d80bf2b-76ee-4975-9ada-a921c8b1cb85
-- title:
--   `BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq` [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) : fderiv ℝ (fderiv ℝ fun y : E => G...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq` [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) : fderiv ℝ (fderiv ℝ fun y : E => G (‖y‖ ^ 2)) x = (2 * deriv G (‖x‖ ^ 2)) • (innerCLM E) + ((4 * deriv (deriv G) (‖x‖ ^ 2)) • innerCLM E x).smulRight (innerCLM E x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.fderiv_fderiv_comp_normSq [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E}
    (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    fderiv ℝ (fderiv ℝ fun y : E => G (‖y‖ ^ 2)) x
      = (2 * deriv G (‖x‖ ^ 2)) • (innerCLM E)
        + ((4 * deriv (deriv G) (‖x‖ ^ 2)) • innerCLM E x).smulRight (innerCLM E x) := by sorry
