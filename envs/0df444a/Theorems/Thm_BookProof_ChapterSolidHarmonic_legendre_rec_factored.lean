-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_legendre_rec_factored
-- name    : BookProof.ChapterSolidHarmonic.legendre_rec_factored
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:19.881012+00:00
-- url     : https://prove2.me/theorems/722e56c8-04fe-4fbc-b83e-b0103fcd64a5
-- title:
--   `BookProof.ChapterSolidHarmonic.legendre_rec_factored` {l μ : ℕ} (hμ : μ ≤ l) (j : ℕ) : ((j : ℝ) + 2) * ((j : ℝ) + 1) * (derivative^[μ] (legendre l)).coeff (j + 2) = -((((l - μ : ℕ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.legendre_rec_factored` {l μ : ℕ} (hμ : μ ≤ l) (j : ℕ) : ((j : ℝ) + 2) * ((j : ℝ) + 1) * (derivative^[μ] (legendre l)).coeff (j + 2) = -((((l - μ : ℕ) : ℝ) - j) * (((l - μ : ℕ) : ℝ) + j + 2 * μ + 1)) * (derivative^[μ] (legendre l)).coeff j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.legendre_rec_factored`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.legendre_rec_factored
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

theorem BookProof.ChapterSolidHarmonic.legendre_rec_factored {l μ : ℕ} (hμ : μ ≤ l) (j : ℕ) :
    ((j : ℝ) + 2) * ((j : ℝ) + 1) * (derivative^[μ] (legendre l)).coeff (j + 2)
      = -((((l - μ : ℕ) : ℝ) - j) * (((l - μ : ℕ) : ℝ) + j + 2 * μ + 1))
        * (derivative^[μ] (legendre l)).coeff j := by sorry
