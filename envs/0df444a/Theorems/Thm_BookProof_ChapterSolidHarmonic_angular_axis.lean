-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_angular_axis
-- name    : BookProof.ChapterSolidHarmonic.angular_axis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:39:50.274738+00:00
-- url     : https://prove2.me/theorems/4b5d3792-6ad6-48ff-b3cc-f2dc46fa57c8
-- title:
--   `BookProof.ChapterSolidHarmonic.angular_axis` {u v e : E} (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (μ : ℕ) (x : E) : fderiv ℝ (angular u v μ) x e = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.angular_axis` {u v e : E} (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (μ : ℕ) (x : E) : fderiv ℝ (angular u v μ) x e = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.angular_axis`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.angular_axis
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

theorem BookProof.ChapterSolidHarmonic.angular_axis {u v e : E} (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (μ : ℕ) (x : E) :
    fderiv ℝ (angular u v μ) x e = 0 := by sorry
