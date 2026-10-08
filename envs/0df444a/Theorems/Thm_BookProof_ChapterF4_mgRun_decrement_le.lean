-- Prove2me | Theorems.Thm_BookProof_ChapterF4_mgRun_decrement_le
-- name    : BookProof.ChapterF4.mgRun_decrement_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:01:48.932147+00:00
-- url     : https://prove2.me/theorems/a72c4f71-93b4-420c-add9-9f1eb7338140
-- title:
--   `BookProof.ChapterF4.mgRun_decrement_le` (k : ℕ) (xs : List ι) : k * (mgRun k xs).2 ≤ xs.length
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.mgRun_decrement_le` (k : ℕ) (xs : List ι) : k * (mgRun k xs).2 ≤ xs.length
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.mgRun_decrement_le`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.mgRun_decrement_le
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BookProof.ChapterF4.mgRun_decrement_le (k : ℕ) (xs : List ι) :
    k * (mgRun k xs).2 ≤ xs.length := by sorry
