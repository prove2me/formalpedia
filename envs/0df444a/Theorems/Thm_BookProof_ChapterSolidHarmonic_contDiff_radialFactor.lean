-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_radialFactor
-- name    : BookProof.ChapterSolidHarmonic.contDiff_radialFactor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:34.468896+00:00
-- url     : https://prove2.me/theorems/5c650689-1d3b-4310-b815-a13cf429aaae
-- title:
--   `BookProof.ChapterSolidHarmonic.contDiff_radialFactor` (e : E) (l μ : ℕ) : ContDiff ℝ 2 (radialFactor e l μ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.contDiff_radialFactor` (e : E) (l μ : ℕ) : ContDiff ℝ 2 (radialFactor e l μ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.contDiff_radialFactor`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.contDiff_radialFactor
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

theorem BookProof.ChapterSolidHarmonic.contDiff_radialFactor (e : E) (l μ : ℕ) : ContDiff ℝ 2 (radialFactor e l μ) := by sorry
