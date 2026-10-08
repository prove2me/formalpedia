-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_norm_unitary_apply
-- name    : BookProof.BrstLeakage.norm_unitary_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:29:57.767568+00:00
-- url     : https://prove2.me/theorems/bb198a60-e288-49c6-bfca-91321520909d
-- title:
--   `BookProof.BrstLeakage.norm_unitary_apply` {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (x : E) : ‖U x‖ = ‖x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.norm_unitary_apply` {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (x : E) : ‖U x‖ = ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.norm_unitary_apply`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.norm_unitary_apply
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.norm_unitary_apply {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (x : E) :
    ‖U x‖ = ‖x‖ := by sorry
