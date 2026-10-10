-- Prove2me | Theorems.Thm_BookProof_ChapterLaplacianProduct_helmholtz_radial_mul_harmonic
-- name    : BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:23:05.175037+00:00
-- url     : https://prove2.me/theorems/e78d2912-1c71-46ab-9495-b2c3363f702a
-- title:
--   `BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic` [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E} {l : ℕ} {p : ℝ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLaplacianProduct`.
--
--   `BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic` [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E} {l : ℕ} {p : ℝ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) (hH : ContDiffAt ℝ 2 H x) (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) (hradial : deriv (deriv g) ‖x‖ + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖) * deriv g ‖x‖ = -(p ^ 2) * g ‖x‖) : -(Δ fun y : E => g ‖y‖ * H y) x = p ^ 2 * (g ‖x‖ * H x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic`.

-- Generated from ChapterLaplacianProduct.lean — theorem BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic
import Definitions.Def_ChapterRadialLaplacian
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterLaplacianProduct



open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic [FiniteDimensional ℝ E] {g : ℝ → ℝ} {H : E → ℝ} {x : E}
    {l : ℕ} {p : ℝ} (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖) (hH : ContDiffAt ℝ 2 H x)
    (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x)
    (hradial : deriv (deriv g) ‖x‖
      + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖) * deriv g ‖x‖ = -(p ^ 2) * g ‖x‖) :
    -(Δ fun y : E => g ‖y‖ * H y) x = p ^ 2 * (g ‖x‖ * H x) := by sorry
