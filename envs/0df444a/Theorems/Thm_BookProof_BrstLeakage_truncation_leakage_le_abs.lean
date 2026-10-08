-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_truncation_leakage_le_abs
-- name    : BookProof.BrstLeakage.truncation_leakage_le_abs
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:17:57.246122+00:00
-- url     : https://prove2.me/theorems/0e0b67ad-26e9-4ec9-bd9f-d3b001ef5d58
-- title:
--   `BookProof.BrstLeakage.truncation_leakage_le_abs` {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P) (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) {x :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.truncation_leakage_le_abs` {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P) (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) {x : E} (hx : P x = x) : ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * |t|)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.truncation_leakage_le_abs`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.truncation_leakage_le_abs
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.truncation_leakage_le_abs {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P)
    (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) {x : E} (hx : P x = x) :
    ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * |t|) := by sorry
