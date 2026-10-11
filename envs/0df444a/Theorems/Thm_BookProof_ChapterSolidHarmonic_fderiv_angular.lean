-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_fderiv_angular
-- name    : BookProof.ChapterSolidHarmonic.fderiv_angular
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:39:06.617112+00:00
-- url     : https://prove2.me/theorems/f9c43937-c12a-4b44-8bae-15f425b260ce
-- title:
--   `BookProof.ChapterSolidHarmonic.fderiv_angular` (u v : E) (μ : ℕ) (x w : E) : fderiv ℝ (angular u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.fderiv_angular` (u v : E) (μ : ℕ) (x w : E) : fderiv ℝ (angular u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).re
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.fderiv_angular`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.fderiv_angular
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

theorem BookProof.ChapterSolidHarmonic.fderiv_angular (u v : E) (μ : ℕ) (x w : E) :
    fderiv ℝ (angular u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).re := by sorry
