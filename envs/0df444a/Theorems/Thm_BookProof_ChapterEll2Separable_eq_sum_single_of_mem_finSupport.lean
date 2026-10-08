-- Prove2me | Theorems.Thm_BookProof_ChapterEll2Separable_eq_sum_single_of_mem_finSupport
-- name    : BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:43:39.808766+00:00
-- url     : https://prove2.me/theorems/3bd4c8f8-f058-4651-92db-e958a8aa448b
-- title:
--   `BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport` (f : Ell2) {s : Finset ℕ} (hs : Function.support ((f : ℕ → ℝ)) ⊆ (s : Set ℕ)) : f = ∑ i ∈ s, lp.single 2 i ((f : ℕ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEll2Separable`.
--
--   `BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport` (f : Ell2) {s : Finset ℕ} (hs : Function.support ((f : ℕ → ℝ)) ⊆ (s : Set ℕ)) : f = ∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport`.

-- Generated from ChapterEll2Separable.lean — theorem BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport
import Mathlib
import Definitions.Def_ChapterEll2Separable
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterRieszFischer
open BookProof.ChapterEll2Separable


open Filter Finset
open scoped ENNReal


open BookProof.ChapterRieszFischer

theorem BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport (f : Ell2) {s : Finset ℕ}
    (hs : Function.support ((f : ℕ → ℝ)) ⊆ (s : Set ℕ)) :
    f = ∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i) := by sorry
