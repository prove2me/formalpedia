-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_deriv_sqrt_comp
-- name    : BookProof.ChapterRadialLaplacian.deriv_sqrt_comp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:58:58.256978+00:00
-- url     : https://prove2.me/theorems/bdf79cd1-a956-40d6-83a4-ad9e01171a8b
-- title:
--   `BookProof.ChapterRadialLaplacian.deriv_sqrt_comp` {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContDiffAt ℝ 2 g r) : deriv (fun q => g (Real.sqrt q)) (r ^ 2) = deriv g r * (1 / (2 * r))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.deriv_sqrt_comp` {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContDiffAt ℝ 2 g r) : deriv (fun q => g (Real.sqrt q)) (r ^ 2) = deriv g r * (1 / (2 * r)) ∧ deriv (deriv fun q => g (Real.sqrt q)) (r ^ 2) = deriv (deriv g) r * (1 / (2 * r)) * (1 / (2 * r)) + deriv g r * (-(1 / (4 * r ^ 3)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.deriv_sqrt_comp`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.deriv_sqrt_comp
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.deriv_sqrt_comp {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContDiffAt ℝ 2 g r) :
    deriv (fun q => g (Real.sqrt q)) (r ^ 2) = deriv g r * (1 / (2 * r)) ∧
    deriv (deriv fun q => g (Real.sqrt q)) (r ^ 2)
      = deriv (deriv g) r * (1 / (2 * r)) * (1 / (2 * r)) + deriv g r * (-(1 / (4 * r ^ 3))) := by sorry
