-- Prove2me | Theorems.Thm_BookProof_ChapterBesselHarmonic_helmholtz_sbessel_harmonic
-- name    : BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:55:25.902712+00:00
-- url     : https://prove2.me/theorems/c5225565-1105-4442-9c84-e6d73f306ca8
-- title:
--   `BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic` [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3) {l : ℕ} {H : E → ℝ} {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) (hH
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBesselHarmonic`.
--
--   `BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic` [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3) {l : ℕ} {H : E → ℝ} {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) (hH : ContDiffAt ℝ 2 H x) (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) : -(Δ fun y : E => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * H y) x = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * H x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic`.

-- Generated from ChapterBesselHarmonic.lean — theorem BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterBesselHarmonic



open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    {l : ℕ} {H : E → ℝ} {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0)
    (hH : ContDiffAt ℝ 2 H x) (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) :
    -(Δ fun y : E => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * H y) x
      = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * H x) := by sorry
