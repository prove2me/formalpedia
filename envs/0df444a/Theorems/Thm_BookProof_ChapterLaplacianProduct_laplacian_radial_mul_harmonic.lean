-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_laplacian_radial_mul_harmonic
-- name    : BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:25:29.148826+00:00
-- url     : https://prove2.me/theorems/6a80f965-fb6c-4805-9994-0a31ad25150a
-- title:
--   `BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic` [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E} {l : ℕ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic` [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E} {l : ℕ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) (hH : ContDiffAt ℝ 2 H x) (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) : (Δ fun y : E => g ‖y‖ * H y) x = (deriv (deriv g) ‖x‖ + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖) * deriv g ‖x‖) * H x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E}
    {l : ℕ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) (hH : ContDiffAt ℝ 2 H x)
    (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) :
    (Δ fun y : E => g ‖y‖ * H y) x
      = (deriv (deriv g) ‖x‖
          + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖) * deriv g ‖x‖) * H x := by sorry
