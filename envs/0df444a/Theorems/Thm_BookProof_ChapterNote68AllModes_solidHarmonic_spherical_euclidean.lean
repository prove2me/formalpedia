-- Prove2me | Theorems.Thm_BookProof_ChapterNote68AllModes_solidHarmonic_spherical_euclidean
-- name    : BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-06T11:43:52.809019+00:00
-- url     : https://prove2.me/theorems/ca4a4406-525b-4e77-b25d-3d9b83680a32
-- title:
--   `BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean` {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) (φ : ℝ) : solidHarmonic (stdVec 0) (st
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNote68AllModes`.
--
--   `BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean` {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) (φ : ℝ) : solidHarmonic (stdVec 0) (stdVec 1) (stdVec 2) l μ (spherePt (stdVec 0) (stdVec 1) (stdVec 2) r θ φ) = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean`.

-- Generated from ChapterNote68AllModes.lean — theorem BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean
import Definitions.Def_ChapterSphericalBessel
import Definitions.Def_ChapterBesselHarmonic
import Definitions.Def_ChapterSolidHarmonic
import Mathlib
import Definitions.Def_ChapterNote68AllModes
open BookProof.ChapterNote68AllModes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterSphericalBessel BookProof.ChapterBesselHarmonic
open BookProof.ChapterSolidHarmonic
open scoped RealInnerProductSpace

theorem BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : 0 ≤ Real.sin θ) (φ : ℝ) :
    solidHarmonic (stdVec 0) (stdVec 1) (stdVec 2) l μ
        (spherePt (stdVec 0) (stdVec 1) (stdVec 2) r θ φ)
      = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ) := by sorry
