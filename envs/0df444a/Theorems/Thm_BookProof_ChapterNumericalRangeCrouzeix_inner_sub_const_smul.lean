-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_inner_sub_const_smul
-- name    : BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:54.205574+00:00
-- url     : https://prove2.me/theorems/d79771b9-8e64-4320-be0e-310d02189b6e
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul` (A : E →L[ℂ] E) (c : ℂ) (x : E) : (⟪ x, (A - c • (1 : E →L[ℂ] E)) x ⟫_ℂ) = ⟪ x, A x ⟫_ℂ - c * (‖x‖ ^ 2 : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul` (A : E →L[ℂ] E) (c : ℂ) (x : E) : (⟪ x, (A - c • (1 : E →L[ℂ] E)) x ⟫_ℂ) = ⟪ x, A x ⟫_ℂ - c * (‖x‖ ^ 2 : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul (A : E →L[ℂ] E) (c : ℂ) (x : E) :
    (⟪ x, (A - c • (1 : E →L[ℂ] E)) x ⟫_ℂ) = ⟪ x, A x ⟫_ℂ - c * (‖x‖ ^ 2 : ℝ) := by sorry
