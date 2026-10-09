-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_flow_truncGen_mem
-- name    : BookProof.BrstLeakage.flow_truncGen_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:17:25.285527+00:00
-- url     : https://prove2.me/theorems/d45acbfb-dfe1-432e-aaa8-f145820b1156
-- title:
--   `BookProof.BrstLeakage.flow_truncGen_mem` {P H : E →L[ℂ] E} (hP : IsIdempotentElem P) (t : ℝ) {x : E} (hx : P x = x) : P (flow (truncGen P H) t x) = flow (truncGen P H) t x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.flow_truncGen_mem` {P H : E →L[ℂ] E} (hP : IsIdempotentElem P) (t : ℝ) {x : E} (hx : P x = x) : P (flow (truncGen P H) t x) = flow (truncGen P H) t x
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.flow_truncGen_mem`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.flow_truncGen_mem
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.flow_truncGen_mem {P H : E →L[ℂ] E} (hP : IsIdempotentElem P) (t : ℝ) {x : E}
    (hx : P x = x) : P (flow (truncGen P H) t x) = flow (truncGen P H) t x := by sorry
