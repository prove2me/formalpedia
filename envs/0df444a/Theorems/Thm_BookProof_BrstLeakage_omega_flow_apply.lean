-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_omega_flow_apply
-- name    : BookProof.BrstLeakage.omega_flow_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:12:33.488019+00:00
-- url     : https://prove2.me/theorems/ab217e46-0018-407a-8cfb-984a1a0e7d0f
-- title:
--   `BookProof.BrstLeakage.omega_flow_apply` {A Om : E →L[ℂ] E} (h : Commute A Om) (t : ℝ) (x : E) : Om (flow A t x) = flow A t (Om x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.omega_flow_apply` {A Om : E →L[ℂ] E} (h : Commute A Om) (t : ℝ) (x : E) : Om (flow A t x) = flow A t (Om x)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.omega_flow_apply`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.omega_flow_apply
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.omega_flow_apply {A Om : E →L[ℂ] E} (h : Commute A Om) (t : ℝ) (x : E) :
    Om (flow A t x) = flow A t (Om x) := by sorry
