-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_diffAt_deriv_of_contDiffAt_two
-- name    : BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:58:48.238982+00:00
-- url     : https://prove2.me/theorems/b6c63c3f-6a7a-4e3b-b5e3-4f156af7c660
-- title:
--   `BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two` {G : ℝ → ℝ} {q : ℝ} (h : ContDiffAt ℝ 2 G q) : DifferentiableAt ℝ (deriv G) q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two` {G : ℝ → ℝ} {q : ℝ} (h : ContDiffAt ℝ 2 G q) : DifferentiableAt ℝ (deriv G) q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.diffAt_deriv_of_contDiffAt_two {G : ℝ → ℝ} {q : ℝ} (h : ContDiffAt ℝ 2 G q) :
    DifferentiableAt ℝ (deriv G) q := by sorry
