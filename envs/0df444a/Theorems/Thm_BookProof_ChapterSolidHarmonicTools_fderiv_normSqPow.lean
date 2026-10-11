-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_fderiv_normSqPow
-- name    : BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:55:47.740224+00:00
-- url     : https://prove2.me/theorems/fc294fcc-28dc-4a9c-aa63-cf2690b4f577
-- title:
--   `BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow` (m : ℕ) (x : E) : fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x = (2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow` (m : ℕ) (x : E) : fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x = (2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow
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

theorem BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow (m : ℕ) (x : E) :
    fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x = (2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x := by sorry
