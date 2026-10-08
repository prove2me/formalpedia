-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_flow_mem_ker_omega
-- name    : BookProof.BrstLeakage.flow_mem_ker_omega
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:12:43.052013+00:00
-- url     : https://prove2.me/theorems/42f90646-2a02-4682-9388-9f10cbd150f1
-- title:
--   `BookProof.BrstLeakage.flow_mem_ker_omega` {A Om : E →L[ℂ] E} (h : Commute A Om) (t : ℝ) {x : E} (hx : Om x = 0) : Om (flow A t x) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.flow_mem_ker_omega` {A Om : E →L[ℂ] E} (h : Commute A Om) (t : ℝ) {x : E} (hx : Om x = 0) : Om (flow A t x) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.flow_mem_ker_omega`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.flow_mem_ker_omega
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.flow_mem_ker_omega {A Om : E →L[ℂ] E} (h : Commute A Om) (t : ℝ) {x : E}
    (hx : Om x = 0) : Om (flow A t x) = 0 := by sorry
