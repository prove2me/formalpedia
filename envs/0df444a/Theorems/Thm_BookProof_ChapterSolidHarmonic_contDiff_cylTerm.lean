-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_cylTerm
-- name    : BookProof.ChapterSolidHarmonic.contDiff_cylTerm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:38.844325+00:00
-- url     : https://prove2.me/theorems/251ee423-b113-4951-91cc-e0a0ad41d168
-- title:
--   `BookProof.ChapterSolidHarmonic.contDiff_cylTerm` (e : E) (j m : ℕ) : ContDiff ℝ 2 fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonic`.
--
--   `BookProof.ChapterSolidHarmonic.contDiff_cylTerm` (e : E) (j m : ℕ) : ContDiff ℝ 2 fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonic.contDiff_cylTerm`.

-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.contDiff_cylTerm
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonic.contDiff_cylTerm (e : E) (j m : ℕ) :
    ContDiff ℝ 2 fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m := by sorry
