-- Prove2me | Theorems.Thm_BookProof_ChapterBesselHarmonic_helmholtz_sbessel_one_clm
-- name    : BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:56:15.660871+00:00
-- url     : https://prove2.me/theorems/3482ef1d-9997-4737-afca-e690a37b4680
-- title:
--   `BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm` [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3) (L : E →L[ℝ] ℝ) {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBesselHarmonic`.
--
--   `BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm` [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3) (L : E →L[ℝ] ℝ) {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : E => (sbessel 1 (p * ‖y‖) / ‖y‖ ^ 1) * L y) x = p ^ 2 * ((sbessel 1 (p * ‖x‖) / ‖x‖ ^ 1) * L x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm`.

-- Generated from ChapterBesselHarmonic.lean — theorem BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm
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

theorem BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    (L : E →L[ℝ] ℝ) {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : E => (sbessel 1 (p * ‖y‖) / ‖y‖ ^ 1) * L y) x
      = p ^ 2 * ((sbessel 1 (p * ‖x‖) / ‖x‖ ^ 1) * L x) := by sorry
