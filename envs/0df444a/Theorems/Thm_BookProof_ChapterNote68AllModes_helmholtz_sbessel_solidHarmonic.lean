-- Prove2me | Theorems.Thm_BookProof_ChapterNote68AllModes_helmholtz_sbessel_solidHarmonic
-- name    : BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-06T10:12:49.164357+00:00
-- url     : https://prove2.me/theorems/fc76e5e6-a281-47fa-b65d-bdb6d50d9ab7
-- title:
--   `BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic` {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNote68AllModes`.
--
--   `BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic` {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (h3 : Module.finrank ℝ E = 3) {l μ : ℕ} (hμ : μ ≤ l) {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : E => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * solidHarmonic u v e l μ y) x = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * solidHarmonic u v e l μ x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic`.

-- Generated from ChapterNote68AllModes.lean — theorem BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic
import Definitions.Def_ChapterBesselHarmonic
import Definitions.Def_ChapterSolidHarmonic
import Mathlib
import Definitions.Def_ChapterNote68AllModes
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterNote68AllModes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterSphericalBessel BookProof.ChapterBesselHarmonic
open BookProof.ChapterSolidHarmonic
open scoped RealInnerProductSpace

theorem BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)
    (h3 : Module.finrank ℝ E = 3) {l μ : ℕ} (hμ : μ ≤ l) {x : E} {p : ℝ}
    (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : E => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * solidHarmonic u v e l μ y) x
      = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * solidHarmonic u v e l μ x) := by sorry
