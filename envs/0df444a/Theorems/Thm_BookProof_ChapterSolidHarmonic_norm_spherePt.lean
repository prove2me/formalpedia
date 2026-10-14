-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_norm_spherePt
-- name    : BookProof.ChapterSolidHarmonic.norm_spherePt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:10:38.39329+00:00
-- url     : https://prove2.me/theorems/f5828578-997f-4c03-aada-ef4bb3883acd
-- title:
--   `BookProof.ChapterSolidHarmonic.norm_spherePt` {r : ℝ} (hr : 0 ≤ r) (θ φ : ℝ) : ‖spherePt u v e r θ φ‖ = r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.norm_spherePt` {r : ℝ} (hr : 0 ≤ r) (θ φ : ℝ) : ‖spherePt u v e r θ φ‖ = r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.norm_spherePt`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.norm_spherePt
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

theorem BookProof.ChapterSolidHarmonic.norm_spherePt {r : ℝ} (hr : 0 ≤ r) (θ φ : ℝ) : ‖spherePt u v e r θ φ‖ = r := by sorry
