-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_helmholtz_sbessel_zero
-- name    : BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:47:04.303857+00:00
-- url     : https://prove2.me/theorems/15ccdcb2-284b-4cf1-b0b0-00bc8f502e58
-- title:
--   `BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero` [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3) {p : ℝ} {x : E} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : E => sbessel
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero` [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3) {p : ℝ} {x : E} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : E => sbessel 0 (p * ‖y‖)) x = p ^ 2 * sbessel 0 (p * ‖x‖)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    {p : ℝ} {x : E} (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : E => sbessel 0 (p * ‖y‖)) x = p ^ 2 * sbessel 0 (p * ‖x‖) := by sorry
