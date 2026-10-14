-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_contDiffAt_sbessel_zero
-- name    : BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:46:52.745879+00:00
-- url     : https://prove2.me/theorems/be8e9f33-a23c-43e2-a1b6-9fd70f9ee84a
-- title:
--   `BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero` {r : ℝ} (hr : r ≠ 0) : ContDiffAt ℝ 2 (sbessel 0) r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero` {r : ℝ} (hr : r ≠ 0) : ContDiffAt ℝ 2 (sbessel 0) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterSphericalBessel
import Definitions.Def_ChapterSphericalBesselODE
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero {r : ℝ} (hr : r ≠ 0) : ContDiffAt ℝ 2 (sbessel 0) r := by sorry
