-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_solidHarmonic_spherical
-- name    : BookProof.ChapterSolidHarmonic.solidHarmonic_spherical
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:10:42.080866+00:00
-- url     : https://prove2.me/theorems/89d5ba0d-319c-4c14-836b-1866c41c9951
-- title:
--   `BookProof.ChapterSolidHarmonic.solidHarmonic_spherical` {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) (φ : ℝ) : solidHarmonic u v e l μ (spherePt u v e
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.solidHarmonic_spherical` {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) (φ : ℝ) : solidHarmonic u v e l μ (spherePt u v e r θ φ) = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.solidHarmonic_spherical`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.solidHarmonic_spherical
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

theorem BookProof.ChapterSolidHarmonic.solidHarmonic_spherical {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : 0 ≤ Real.sin θ) (φ : ℝ) :
    solidHarmonic u v e l μ (spherePt u v e r θ φ)
      = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ) := by sorry
