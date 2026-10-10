-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_fderiv_comp_normSq
-- name    : BookProof.ChapterRadialLaplacian.fderiv_comp_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:58:21.69899+00:00
-- url     : https://prove2.me/theorems/57d6b8b5-5bf0-46f8-906c-a55dae0c0224
-- title:
--   `BookProof.ChapterRadialLaplacian.fderiv_comp_normSq` {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) : (fderiv ℝ fun z : E => G (‖z‖ ^ 2)) =ᶠ[nhds x] fun y => (2 * deriv G (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.fderiv_comp_normSq` {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) : (fderiv ℝ fun z : E => G (‖z‖ ^ 2)) =ᶠ[nhds x] fun y => (2 * deriv G (‖y‖ ^ 2)) • (innerCLM E y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.fderiv_comp_normSq`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.fderiv_comp_normSq
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.fderiv_comp_normSq {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    (fderiv ℝ fun z : E => G (‖z‖ ^ 2)) =ᶠ[nhds x]
      fun y => (2 * deriv G (‖y‖ ^ 2)) • (innerCLM E y) := by sorry
