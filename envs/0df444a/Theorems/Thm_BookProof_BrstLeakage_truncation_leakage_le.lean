-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_truncation_leakage_le
-- name    : BookProof.BrstLeakage.truncation_leakage_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:16:57.652748+00:00
-- url     : https://prove2.me/theorems/7bc5c3aa-07b9-4768-895e-50a65dcbbd04
-- title:
--   `BookProof.BrstLeakage.truncation_leakage_le` {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P) (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (ht : 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.truncation_leakage_le` {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P) (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : P x = x) : ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.truncation_leakage_le`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.truncation_leakage_le
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.truncation_leakage_le {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P)
    (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : P x = x) :
    ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * t) := by sorry
