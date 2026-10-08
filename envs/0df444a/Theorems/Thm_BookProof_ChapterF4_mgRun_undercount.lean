-- Prove2me | Theorems.Thm_BookProof_ChapterF4_mgRun_undercount
-- name    : BookProof.ChapterF4.mgRun_undercount
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:01:33.768976+00:00
-- url     : https://prove2.me/theorems/72f614bc-8318-48e7-a5ef-d07801af0a70
-- title:
--   `BookProof.ChapterF4.mgRun_undercount` (k : ℕ) (xs : List ι) (x : ι) : (mgRun k xs).1 x ≤ xs.count x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.mgRun_undercount` (k : ℕ) (xs : List ι) (x : ι) : (mgRun k xs).1 x ≤ xs.count x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.mgRun_undercount`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.mgRun_undercount
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

theorem BookProof.ChapterF4.mgRun_undercount (k : ℕ) (xs : List ι) (x : ι) :
    (mgRun k xs).1 x ≤ xs.count x := by sorry
