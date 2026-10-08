-- Prove2me | Theorems.Thm_BookProof_ChapterF4_selfAdjoint_exp_star_mul_self
-- name    : BookProof.ChapterF4.selfAdjoint_exp_star_mul_self
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:50:33.613872+00:00
-- url     : https://prove2.me/theorems/e69aa8a1-4a69-4b43-91c1-6228c893fbba
-- title:
--   `BookProof.ChapterF4.selfAdjoint_exp_star_mul_self` (h : selfAdjoint A) : star ((selfAdjoint.expUnitary h : A)) * (selfAdjoint.expUnitary h : A) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.selfAdjoint_exp_star_mul_self` (h : selfAdjoint A) : star ((selfAdjoint.expUnitary h : A)) * (selfAdjoint.expUnitary h : A) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.selfAdjoint_exp_star_mul_self`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.selfAdjoint_exp_star_mul_self
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

theorem BookProof.ChapterF4.selfAdjoint_exp_star_mul_self (h : selfAdjoint A) :
    star ((selfAdjoint.expUnitary h : A)) * (selfAdjoint.expUnitary h : A) = 1 := by sorry
