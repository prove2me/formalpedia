-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_hasFDerivAt_radialFactor
-- name    : BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:14.586285+00:00
-- url     : https://prove2.me/theorems/c427a14b-c4f8-4764-8e5b-0c534a81bc43
-- title:
--   `BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor` (e : E) (l μ : ℕ) (x : E) : HasFDerivAt (radialFactor e l μ) (∑ m ∈ Finset.range ((l - μ) / 2 + 1), ((derivative^[μ] (lege
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor` (e : E) (l μ : ℕ) (x : E) : HasFDerivAt (radialFactor e l μ) (∑ m ∈ Finset.range ((l - μ) / 2 + 1), ((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)) • ((((l - μ - 2 * m : ℕ) : ℝ) * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e + (2 * m * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m) * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor
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

theorem BookProof.ChapterSolidHarmonic.hasFDerivAt_radialFactor (e : E) (l μ : ℕ) (x : E) :
    HasFDerivAt (radialFactor e l μ)
      (∑ m ∈ Finset.range ((l - μ) / 2 + 1),
        ((derivative^[μ] (legendre l)).coeff (l - μ - 2 * m)) •
          ((((l - μ - 2 * m : ℕ) : ℝ) * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m - 1) * (‖x‖ ^ 2) ^ m)
              • innerCLM E e
            + (2 * m * (⟪e, x⟫_ℝ) ^ (l - μ - 2 * m) * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x)) x := by sorry
