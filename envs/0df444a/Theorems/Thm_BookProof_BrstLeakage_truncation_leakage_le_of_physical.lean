-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_truncation_leakage_le_of_physical
-- name    : BookProof.BrstLeakage.truncation_leakage_le_of_physical
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:17:04.679269+00:00
-- url     : https://prove2.me/theorems/d1324cad-0320-4773-8ef7-d2fcb3c152f9
-- title:
--   `BookProof.BrstLeakage.truncation_leakage_le_of_physical` {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P) (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.truncation_leakage_le_of_physical` {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P) (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : P x = x) (hOm : Om x = 0) : ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.truncation_leakage_le_of_physical`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.truncation_leakage_le_of_physical
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.truncation_leakage_le_of_physical {P H Om : E →L[ℂ] E} (hPi : IsIdempotentElem P)
    (hPs : IsSelfAdjoint P) (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : P x = x) (hOm : Om x = 0) :
    ‖Om (flow (truncGen P H) t x)‖ ≤ ‖Om‖ * (‖(1 - P) * H * P‖ * ‖x‖ * t) := by sorry
