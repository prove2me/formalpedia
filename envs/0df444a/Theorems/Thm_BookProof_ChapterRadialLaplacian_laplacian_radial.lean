-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_laplacian_radial
-- name    : BookProof.ChapterRadialLaplacian.laplacian_radial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:59:00.920315+00:00
-- url     : https://prove2.me/theorems/c6829abe-d573-4600-bd95-4f9870b9b228
-- title:
--   `BookProof.ChapterRadialLaplacian.laplacian_radial` [FiniteDimensional ℝ E] {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) : (Δ fun y : E => g ‖y‖) x = deriv...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.laplacian_radial` [FiniteDimensional ℝ E] {g : ℝ → ℝ} {x : E} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) : (Δ fun y : E => g ‖y‖) x = deriv (deriv g) ‖x‖ + (((Module.finrank ℝ E : ℝ) - 1) / ‖x‖) * deriv g ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.laplacian_radial`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.laplacian_radial
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.laplacian_radial [FiniteDimensional ℝ E] {g : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hg : ContDiffAt ℝ 2 g ‖x‖) :
    (Δ fun y : E => g ‖y‖) x
      = deriv (deriv g) ‖x‖
        + (((Module.finrank ℝ E : ℝ) - 1) / ‖x‖) * deriv g ‖x‖ := by sorry
