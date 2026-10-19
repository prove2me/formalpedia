-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_laplacian_comp_normSq
-- name    : BookProof.ChapterRadialLaplacian.laplacian_comp_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T22:59:47.601165+00:00
-- url     : https://prove2.me/theorems/61c84f44-01ac-41d0-ab31-79dee487d2dd
-- title:
--   `BookProof.ChapterRadialLaplacian.laplacian_comp_normSq` [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) : (Δ fun y : E => G (‖y‖ ^ 2)) x = 4 *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.laplacian_comp_normSq` [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E} (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) : (Δ fun y : E => G (‖y‖ ^ 2)) x = 4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2) + 2 * (Module.finrank ℝ E) * deriv G (‖x‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.laplacian_comp_normSq`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.laplacian_comp_normSq
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.laplacian_comp_normSq [FiniteDimensional ℝ E] {G : ℝ → ℝ} {x : E}
    (hG : ContDiffAt ℝ 2 G (‖x‖ ^ 2)) :
    (Δ fun y : E => G (‖y‖ ^ 2)) x
      = 4 * ‖x‖ ^ 2 * deriv (deriv G) (‖x‖ ^ 2)
        + 2 * (Module.finrank ℝ E) * deriv G (‖x‖ ^ 2) := by sorry
