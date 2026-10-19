-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_u_spherePt
-- name    : BookProof.ChapterSolidHarmonic.inner_u_spherePt
-- status  : Disproved
-- author  : @leonardopedro
-- created : 2026-10-11T20:10:24.568396+00:00
-- url     : https://prove2.me/theorems/2b876f59-bc48-45fe-8790-3ed11b39cf1b
-- title:
--   `BookProof.ChapterSolidHarmonic.inner_u_spherePt` (r θ φ : ℝ) : ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.inner_u_spherePt` (r θ φ : ℝ) : ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.inner_u_spherePt`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.inner_u_spherePt
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

theorem BookProof.ChapterSolidHarmonic.inner_u_spherePt (r θ φ : ℝ) :
    ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ := by sorry
