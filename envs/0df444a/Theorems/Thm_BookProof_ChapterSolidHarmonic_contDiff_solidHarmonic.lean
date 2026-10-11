-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_solidHarmonic
-- name    : BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:54:23.234978+00:00
-- url     : https://prove2.me/theorems/8c42efe0-bd0a-44a1-8940-670e2c34b901
-- title:
--   `BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic` (u v e : E) (l μ : ℕ) : ContDiff ℝ 2 (solidHarmonic u v e l μ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic` (u v e : E) (l μ : ℕ) : ContDiff ℝ 2 (solidHarmonic u v e l μ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic
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

theorem BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic (u v e : E) (l μ : ℕ) : ContDiff ℝ 2 (solidHarmonic u v e l μ) := by sorry
