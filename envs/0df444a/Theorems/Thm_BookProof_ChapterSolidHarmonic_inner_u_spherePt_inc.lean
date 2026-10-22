-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_u_spherePt_inc
-- name    : BookProof.ChapterSolidHarmonic.inner_u_spherePt_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:09.75563+00:00
-- url     : https://prove2.me/theorems/bde6785f-a3be-4982-91c5-946c56e8ee5b
-- title:
--   `BookProof.ChapterSolidHarmonic.inner_u_spherePt_inc` (r θ φ : ℝ) : ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.inner_u_spherePt_inc` (r θ φ : ℝ) : ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.inner_u_spherePt_inc`.
--
--   Replaces the retired node `BookProof.ChapterSolidHarmonic.inner_u_spherePt`, whose stored statement omitted the `he`, `hu`, `hue`, `huv`, `hv`, `hve` hypothesis binder (dropped `include`).

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.inner_u_spherePt_inc
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

include he hu hue huv hv hve in

theorem BookProof.ChapterSolidHarmonic.inner_u_spherePt_inc (r θ φ : ℝ) :
    ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ := by sorry
