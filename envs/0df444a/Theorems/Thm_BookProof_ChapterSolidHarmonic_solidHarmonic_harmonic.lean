-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_solidHarmonic_harmonic
-- name    : BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:12.565824+00:00
-- url     : https://prove2.me/theorems/4a431a95-e9f1-4c0d-a9ff-28d0df9366e4
-- title:
--   `BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic` {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic` {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (h3 : Module.finrank ℝ E = 3) {l μ : ℕ} (hμ : μ ≤ l) (x : E) : (Δ (solidHarmonic u v e l μ)) x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic
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

theorem BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)
    (h3 : Module.finrank ℝ E = 3) {l μ : ℕ} (hμ : μ ≤ l) (x : E) :
    (Δ (solidHarmonic u v e l μ)) x = 0 := by sorry
