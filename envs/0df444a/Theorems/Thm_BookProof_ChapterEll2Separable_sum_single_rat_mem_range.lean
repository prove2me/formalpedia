-- Prove2me | Theorems.Thm_BookProof_ChapterEll2Separable_sum_single_rat_mem_range
-- name    : BookProof.ChapterEll2Separable.sum_single_rat_mem_range
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:44:09.3135+00:00
-- url     : https://prove2.me/theorems/c5310d74-58e0-463f-b0c1-d35abbaab50b
-- title:
--   `BookProof.ChapterEll2Separable.sum_single_rat_mem_range` (s : Finset ℕ) (q : ℕ → ℚ) : (∑ i ∈ s, lp.single 2 i ((q i : ℝ))) ∈ Set.range ratVec
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEll2Separable`.
--
--   `BookProof.ChapterEll2Separable.sum_single_rat_mem_range` (s : Finset ℕ) (q : ℕ → ℚ) : (∑ i ∈ s, lp.single 2 i ((q i : ℝ))) ∈ Set.range ratVec
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEll2Separable.sum_single_rat_mem_range`.

-- Generated from ChapterEll2Separable.lean — theorem BookProof.ChapterEll2Separable.sum_single_rat_mem_range
import Mathlib
import Definitions.Def_ChapterEll2Separable
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterRieszFischer
open BookProof.ChapterEll2Separable


open Filter Finset
open scoped ENNReal


open BookProof.ChapterRieszFischer

theorem BookProof.ChapterEll2Separable.sum_single_rat_mem_range (s : Finset ℕ) (q : ℕ → ℚ) :
    (∑ i ∈ s, lp.single 2 i ((q i : ℝ))) ∈ Set.range ratVec := by sorry
