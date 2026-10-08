-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_flow_mem_unitary
-- name    : BookProof.BrstLeakage.flow_mem_unitary
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:12:22.750306+00:00
-- url     : https://prove2.me/theorems/4bb09c64-08b8-43be-8822-ad8ca9ed6f3e
-- title:
--   `BookProof.BrstLeakage.flow_mem_unitary` {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) : flow A t ∈ unitary (E →L[ℂ] E)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.flow_mem_unitary` {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) : flow A t ∈ unitary (E →L[ℂ] E)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.flow_mem_unitary`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.flow_mem_unitary
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.flow_mem_unitary {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) :
    flow A t ∈ unitary (E →L[ℂ] E) := by sorry
