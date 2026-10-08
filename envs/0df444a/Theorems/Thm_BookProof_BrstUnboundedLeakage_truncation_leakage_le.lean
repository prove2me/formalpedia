-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_truncation_leakage_le
-- name    : BookProof.BrstUnboundedLeakage.truncation_leakage_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:20:12.044335+00:00
-- url     : https://prove2.me/theorems/ca8d0580-bf58-44ec-8e2f-d9da20eae8cf
-- title:
--   `BookProof.BrstUnboundedLeakage.truncation_leakage_le` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.truncation_leakage_le` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) : ‖Om (flow (truncGen T V hV) t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (‖truncDefect T V hV‖ * ‖x‖ * t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.truncation_leakage_le`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.truncation_leakage_le
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.truncation_leakage_le {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) :
    ‖Om (flow (truncGen T V hV) t x)‖
      ≤ ‖Om x‖ + ‖Om‖ * (‖truncDefect T V hV‖ * ‖x‖ * t) := by sorry
