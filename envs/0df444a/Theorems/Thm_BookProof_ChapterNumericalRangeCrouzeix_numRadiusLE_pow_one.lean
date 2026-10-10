-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numRadiusLE_pow_one
-- name    : BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:14:30.542875+00:00
-- url     : https://prove2.me/theorems/bfabbbaa-1f38-4e52-89ff-858dc688933b
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one` {A : E →L[ℂ] E} (h : NumRadiusLE A 1) (n : ℕ) (hn : 0 < n) : NumRadiusLE (A ^ n) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one` {A : E →L[ℂ] E} (h : NumRadiusLE A 1) (n : ℕ) (hn : 0 < n) : NumRadiusLE (A ^ n) 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow_one {A : E →L[ℂ] E} (h : NumRadiusLE A 1) (n : ℕ) (hn : 0 < n) :
    NumRadiusLE (A ^ n) 1 := by sorry
