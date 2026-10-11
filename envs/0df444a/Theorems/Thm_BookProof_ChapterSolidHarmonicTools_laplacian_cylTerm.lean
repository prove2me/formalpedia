-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_cylTerm
-- name    : BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:17:11.141388+00:00
-- url     : https://prove2.me/theorems/1d71679d-9476-4bde-859d-84175f06f099
-- title:
--   `BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm` (e : E) (he : ‖e‖ = 1) (j m : ℕ) (x : E) : (Δ fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x = (j : ℝ) * ((j : ℝ) - 1)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm` (e : E) (he : ‖e‖ = 1) (j m : ℕ) (x : E) : (Δ fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x = (j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m) * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm (e : E) (he : ‖e‖ = 1) (j m : ℕ) (x : E) :
    (Δ fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x
      = (j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m)
            * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1) := by sorry
