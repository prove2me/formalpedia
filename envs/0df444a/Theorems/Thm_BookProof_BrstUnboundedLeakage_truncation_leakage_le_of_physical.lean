-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_truncation_leakage_le_of_physical
-- name    : BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:20:17.676302+00:00
-- url     : https://prove2.me/theorems/36026caa-8aef-4471-8706-46d2794b8dbc
-- title:
--   `BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (ht : 0 ≤ t) {x : H}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) (hOm : Om x = 0) : ‖Om (flow (truncGen T V hV) t x)‖ ≤ ‖Om‖ * (‖truncDefect T V hV‖ * ‖x‖ * t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical
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

theorem BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) (hOm : Om x = 0) :
    ‖Om (flow (truncGen T V hV) t x)‖ ≤ ‖Om‖ * (‖truncDefect T V hV‖ * ‖x‖ * t) := by sorry
