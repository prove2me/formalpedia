-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numRadiusLE_of_re_inner_sub_smul_nonneg
-- name    : BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:14:59.208959+00:00
-- url     : https://prove2.me/theorems/449fd0d0-1127-4083-9e7e-643f7775545e
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg` {A : E →L[ℂ] E} (h : ∀ z : ℂ, ‖z‖ < 1 → ∀ x : E, 0 ≤ (⟪x, x - z • A x⟫_ℂ).re) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg` {A : E →L[ℂ] E} (h : ∀ z : ℂ, ‖z‖ < 1 → ∀ x : E, 0 ≤ (⟪x, x - z • A x⟫_ℂ).re) : NumRadiusLE A 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg {A : E →L[ℂ] E}
    (h : ∀ z : ℂ, ‖z‖ < 1 → ∀ x : E, 0 ≤ (⟪x, x - z • A x⟫_ℂ).re) : NumRadiusLE A 1 := by sorry
