-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_fderiv_angularIm
-- name    : BookProof.ChapterSolidHarmonic.fderiv_angularIm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:39:34.513754+00:00
-- url     : https://prove2.me/theorems/6ebbb27b-d378-4166-b456-b269dc649e62
-- title:
--   `BookProof.ChapterSolidHarmonic.fderiv_angularIm` (u v : E) (μ : ℕ) (x w : E) : fderiv ℝ (angularIm u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).im
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.fderiv_angularIm` (u v : E) (μ : ℕ) (x w : E) : fderiv ℝ (angularIm u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).im
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.fderiv_angularIm`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.fderiv_angularIm
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

theorem BookProof.ChapterSolidHarmonic.fderiv_angularIm (u v : E) (μ : ℕ) (x w : E) :
    fderiv ℝ (angularIm u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).im := by sorry
