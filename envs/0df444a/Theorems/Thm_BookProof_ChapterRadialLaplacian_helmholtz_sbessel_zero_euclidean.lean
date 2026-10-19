-- Prove2me | Theorems.Thm_BookProof_ChapterRadialLaplacian_helmholtz_sbessel_zero_euclidean
-- name    : BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:47:39.860999+00:00
-- url     : https://prove2.me/theorems/eb72f912-4d00-44ff-8ae8-a96d698da038
-- title:
--   `BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean` {p : ℝ} {x : EuclideanSpace ℝ (Fin 3)} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : EuclideanSpace ℝ (Fin 3) => sbess
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRadialLaplacian`.
--
--   `BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean` {p : ℝ} {x : EuclideanSpace ℝ (Fin 3)} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : EuclideanSpace ℝ (Fin 3) => sbessel 0 (p * ‖y‖)) x = p ^ 2 * sbessel 0 (p * ‖x‖)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean`.

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean {p : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : EuclideanSpace ℝ (Fin 3) => sbessel 0 (p * ‖y‖)) x
      = p ^ 2 * sbessel 0 (p * ‖x‖) := by sorry
