-- Prove2me | Theorems.Thm_BookProof_ChapterH7_compress_isSelfAdjoint
-- name    : BookProof.ChapterH7.compress_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:47:21.105994+00:00
-- url     : https://prove2.me/theorems/8fa60f19-f828-4fb5-8366-8cf36f61391c
-- title:
--   `BookProof.ChapterH7.compress_isSelfAdjoint` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) : IsSelfAdjoint (compress V X)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.compress_isSelfAdjoint` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) : IsSelfAdjoint (compress V X)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.compress_isSelfAdjoint`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.compress_isSelfAdjoint
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH7.compress_isSelfAdjoint (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (compress V X) := by sorry
