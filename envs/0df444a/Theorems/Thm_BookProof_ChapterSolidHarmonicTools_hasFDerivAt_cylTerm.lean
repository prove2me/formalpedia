-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonicTools_hasFDerivAt_cylTerm
-- name    : BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:16:41.356473+00:00
-- url     : https://prove2.me/theorems/8c0ec2c2-4866-4a51-a3f4-2afa07bb4472
-- title:
--   `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm` (e : E) (j m : ℕ) (x : E) : HasFDerivAt (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolidHarmonicTools`.
--
--   `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm` (e : E) (j m : ℕ) (x : E) : HasFDerivAt (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e + (2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm`.

-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm
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

theorem BookProof.ChapterSolidHarmonicTools.hasFDerivAt_cylTerm (e : E) (j m : ℕ) (x : E) :
    HasFDerivAt (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m)
      (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e
        + (2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x) x := by sorry
