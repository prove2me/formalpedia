-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_truncGen_isSelfAdjoint
-- name    : BookProof.BrstLeakage.truncGen_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:16:43.68357+00:00
-- url     : https://prove2.me/theorems/29b28b24-b8ec-46d5-8499-8f569f83e7f1
-- title:
--   `BookProof.BrstLeakage.truncGen_isSelfAdjoint` {P H : E →L[ℂ] E} (hP : IsSelfAdjoint P) (hH : IsSelfAdjoint H) : IsSelfAdjoint (truncGen P H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.truncGen_isSelfAdjoint` {P H : E →L[ℂ] E} (hP : IsSelfAdjoint P) (hH : IsSelfAdjoint H) : IsSelfAdjoint (truncGen P H)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.truncGen_isSelfAdjoint`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.truncGen_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.truncGen_isSelfAdjoint {P H : E →L[ℂ] E} (hP : IsSelfAdjoint P)
    (hH : IsSelfAdjoint H) : IsSelfAdjoint (truncGen P H) := by sorry
