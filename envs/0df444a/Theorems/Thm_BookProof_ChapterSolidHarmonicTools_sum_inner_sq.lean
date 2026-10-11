-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_sum_inner_sq
-- name    : BookProof.ChapterSolidHarmonicTools.sum_inner_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:37.146865+00:00
-- url     : https://prove2.me/theorems/d7919996-c73c-467a-85d1-c2778517c2c0
-- title:
--   `BookProof.ChapterSolidHarmonicTools.sum_inner_sq` (e : E) : ∑ i, (⟪e, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 = ‖e‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.sum_inner_sq` (e : E) : ∑ i, (⟪e, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 = ‖e‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.sum_inner_sq`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.sum_inner_sq
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.sum_inner_sq (e : E) :
    ∑ i, (⟪e, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 = ‖e‖ ^ 2 := by sorry
