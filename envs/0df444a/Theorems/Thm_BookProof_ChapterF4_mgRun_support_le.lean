-- Prove2me | Theorems.Thm_BookProof_ChapterF4_mgRun_support_le
-- name    : BookProof.ChapterF4.mgRun_support_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:51:34.651577+00:00
-- url     : https://prove2.me/theorems/8c5a24f1-8a24-4644-90f4-df66f3cacbe2
-- title:
--   `BookProof.ChapterF4.mgRun_support_le` (k : ℕ) (xs : List ι) : mgSupport (mgRun k xs).1 ≤ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.mgRun_support_le` (k : ℕ) (xs : List ι) : mgSupport (mgRun k xs).1 ≤ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.mgRun_support_le`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.mgRun_support_le
import Mathlib
import Definitions.Def_ChapterF4
import Definitions.Def_ChapterF6
open BookProof.ChapterF6
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BookProof.ChapterF4.mgRun_support_le (k : ℕ) (xs : List ι) :
    mgSupport (mgRun k xs).1 ≤ k := by sorry
