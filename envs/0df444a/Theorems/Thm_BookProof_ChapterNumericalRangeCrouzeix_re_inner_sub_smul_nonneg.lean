-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_re_inner_sub_smul_nonneg
-- name    : BookProof.ChapterNumericalRangeCrouzeix.re_inner_sub_smul_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:51.889982+00:00
-- url     : https://prove2.me/theorems/10235303-49dd-4da7-98cb-509f62529ef7
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.re_inner_sub_smul_nonneg` {A : E →L[ℂ] E} (h : NumRadiusLE A 1) {z : ℂ} (hz : ‖z‖ ≤ 1) (x : E) : 0 ≤ (⟪x, x - z • A x⟫_ℂ).re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.re_inner_sub_smul_nonneg` {A : E →L[ℂ] E} (h : NumRadiusLE A 1) {z : ℂ} (hz : ‖z‖ ≤ 1) (x : E) : 0 ≤ (⟪x, x - z • A x⟫_ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.re_inner_sub_smul_nonneg`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.re_inner_sub_smul_nonneg
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.re_inner_sub_smul_nonneg {A : E →L[ℂ] E} (h : NumRadiusLE A 1) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (x : E) : 0 ≤ (⟪x, x - z • A x⟫_ℂ).re := by sorry
