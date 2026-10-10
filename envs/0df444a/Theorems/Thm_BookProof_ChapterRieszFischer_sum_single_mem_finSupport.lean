-- Prove2me | Theorems.Thm_BookProof_ChapterRieszFischer_sum_single_mem_finSupport
-- name    : BookProof.ChapterRieszFischer.sum_single_mem_finSupport
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:19:01.444248+00:00
-- url     : https://prove2.me/theorems/9703a0ab-e8ce-4172-86c5-0bd921a2e113
-- title:
--   `BookProof.ChapterRieszFischer.sum_single_mem_finSupport` (f : Ell2) (s : Finset ℕ) : (∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i)) ∈ FinSupport
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRieszFischer`.
--
--   `BookProof.ChapterRieszFischer.sum_single_mem_finSupport` (f : Ell2) (s : Finset ℕ) : (∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i)) ∈ FinSupport
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRieszFischer.sum_single_mem_finSupport`.

-- Generated from ChapterRieszFischer.lean — theorem BookProof.ChapterRieszFischer.sum_single_mem_finSupport
import Mathlib
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterRieszFischer


open Filter
open scoped ENNReal

theorem BookProof.ChapterRieszFischer.sum_single_mem_finSupport (f : Ell2) (s : Finset ℕ) :
    (∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i)) ∈ FinSupport := by sorry
