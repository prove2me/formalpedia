-- Prove2me | Theorems.Thm_BookProof_ChapterNote68AllModes_helmholtz_sbessel_solidHarmonic_euclidean
-- name    : BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-06T11:43:36.948975+00:00
-- url     : https://prove2.me/theorems/6e80b1eb-9396-4937-8897-8bd0c4d0d836
-- title:
--   `BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean` {l μ : ℕ} (hμ : μ ≤ l) {x : EuclideanSpace ℝ (Fin 3)} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : Eu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNote68AllModes`.
--
--   `BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean` {l μ : ℕ} (hμ : μ ≤ l) {x : EuclideanSpace ℝ (Fin 3)} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) : -(Δ fun y : EuclideanSpace ℝ (Fin 3) => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * solidHarmonic (stdVec 0) (stdVec 1) (stdVec 2) l μ y) x = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * solidHarmonic (stdVec 0) (stdVec 1) (stdVec 2) l μ x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean`.

-- Generated from ChapterNote68AllModes.lean — theorem BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean
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

theorem BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean {l μ : ℕ} (hμ : μ ≤ l)
    {x : EuclideanSpace ℝ (Fin 3)} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) :
    -(Δ fun y : EuclideanSpace ℝ (Fin 3) =>
        (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * solidHarmonic (stdVec 0) (stdVec 1) (stdVec 2) l μ y) x
      = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l)
          * solidHarmonic (stdVec 0) (stdVec 1) (stdVec 2) l μ x) := by sorry
