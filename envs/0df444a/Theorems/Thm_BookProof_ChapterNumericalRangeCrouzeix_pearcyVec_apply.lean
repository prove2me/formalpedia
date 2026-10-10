-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_pearcyVec_apply
-- name    : BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:59.01214+00:00
-- url     : https://prove2.me/theorems/1a353d23-7368-4873-a914-d022634a03ea
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply` (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) (y : E) : pearcyVec A c n y - c • A (pearcyVec A c n y) = y - c ^ n • (A ^ n) y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply` (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) (y : E) : pearcyVec A c n y - c • A (pearcyVec A c n y) = y - c ^ n • (A ^ n) y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) (y : E) :
    pearcyVec A c n y - c • A (pearcyVec A c n y) = y - c ^ n • (A ^ n) y := by sorry
