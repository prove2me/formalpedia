-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_radialFactor_euler
-- name    : BookProof.ChapterSolidHarmonic.radialFactor_euler
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:17:22.051868+00:00
-- url     : https://prove2.me/theorems/a24fc47b-d4a3-494d-9ecb-330bfd620d4d
-- title:
--   `BookProof.ChapterSolidHarmonic.radialFactor_euler` (e : E) (l μ : ℕ) (x : E) : fderiv ℝ (radialFactor e l μ) x x = ((l - μ : ℕ) : ℝ) * radialFactor e l μ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.radialFactor_euler` (e : E) (l μ : ℕ) (x : E) : fderiv ℝ (radialFactor e l μ) x x = ((l - μ : ℕ) : ℝ) * radialFactor e l μ x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.radialFactor_euler`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.radialFactor_euler
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterLegendrePolynomial
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterLegendrePolynomial
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonic.radialFactor_euler (e : E) (l μ : ℕ) (x : E) :
    fderiv ℝ (radialFactor e l μ) x x = ((l - μ : ℕ) : ℝ) * radialFactor e l μ x := by sorry
