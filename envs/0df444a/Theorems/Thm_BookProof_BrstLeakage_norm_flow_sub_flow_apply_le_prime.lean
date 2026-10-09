-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_norm_flow_sub_flow_apply_le_prime
-- name    : BookProof.BrstLeakage.norm_flow_sub_flow_apply_le_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:15.43944+00:00
-- url     : https://prove2.me/theorems/f99d1fae-4bb1-4a29-9cef-f78b55b0886f
-- title:
--   BookProof.BrstLeakage.norm_flow_sub_flow_apply_le'
-- statement:
--   BookProof.BrstLeakage.norm_flow_sub_flow_apply_le'

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.norm_flow_sub_flow_apply_le'
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.norm_flow_sub_flow_apply_le_prime {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) (t : ℝ) (ht : 0 ≤ t) (x : E) :
    ‖flow B t x - flow A t x‖ ≤ ‖A - B‖ * ‖x‖ * t := by sorry
