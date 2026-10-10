-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_sum_pearcyVec
-- name    : BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:14:24.599982+00:00
-- url     : https://prove2.me/theorems/54c248b1-149e-42be-a824-75fa4fd3e1cd
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec` {A : E →L[ℂ] E} {w : ℂ} {n : ℕ} (hn : 0 < n) (hw : IsPrimitiveRoot w n) (z : ℂ) (y : E) : ∑ k ∈ Finset.range n, pearcyVec A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec` {A : E →L[ℂ] E} {w : ℂ} {n : ℕ} (hn : 0 < n) (hw : IsPrimitiveRoot w n) (z : ℂ) (y : E) : ∑ k ∈ Finset.range n, pearcyVec A (w ^ k * z) n y = (n : ℂ) • y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.sum_pearcyVec {A : E →L[ℂ] E} {w : ℂ} {n : ℕ} (hn : 0 < n)
    (hw : IsPrimitiveRoot w n) (z : ℂ) (y : E) :
    ∑ k ∈ Finset.range n, pearcyVec A (w ^ k * z) n y = (n : ℂ) • y := by sorry
