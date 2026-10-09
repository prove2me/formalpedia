-- Prove2me | Theorems.Thm_BookProof_ChapterH7_inner_self_real
-- name    : BookProof.ChapterH7.inner_self_real
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:53:21.718194+00:00
-- url     : https://prove2.me/theorems/b9fc02b3-22ae-4582-96d9-543e617faf24
-- title:
--   `BookProof.ChapterH7.inner_self_real` (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (x : E) : (inner ℂ x (X x) : ℂ).im = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.inner_self_real` (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (x : E) : (inner ℂ x (X x) : ℂ).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.inner_self_real`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.inner_self_real
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH7
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH7.inner_self_real (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (x : E) :
    (inner ℂ x (X x) : ℂ).im = 0 := by sorry
