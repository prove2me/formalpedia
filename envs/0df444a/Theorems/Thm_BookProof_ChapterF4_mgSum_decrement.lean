-- Prove2me | Theorems.Thm_BookProof_ChapterF4_mgSum_decrement
-- name    : BookProof.ChapterF4.mgSum_decrement
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:52:16.75255+00:00
-- url     : https://prove2.me/theorems/a4cd6c68-f354-4ca5-a21f-43aa326204cf
-- title:
--   `BookProof.ChapterF4.mgSum_decrement` (c : ι → ℕ) : (∑ a, (c a - 1)) + mgSupport c = ∑ a, c a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.mgSum_decrement` (c : ι → ℕ) : (∑ a, (c a - 1)) + mgSupport c = ∑ a, c a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.mgSum_decrement`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.mgSum_decrement
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

theorem BookProof.ChapterF4.mgSum_decrement (c : ι → ℕ) :
    (∑ a, (c a - 1)) + mgSupport c = ∑ a, c a := by sorry
