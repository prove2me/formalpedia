-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_flow_truncGen_sub_stoneU_le
-- name    : BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:20:04.411228+00:00
-- url     : https://prove2.me/theorems/73d01b31-c577-420f-ae66-e472574445a8
-- title:
--   `BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le` (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) : ‖flow (truncGen T V hV) t x - T.stoneU t x‖ ≤ ‖truncDefect T V hV‖ * ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le` (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) : ‖flow (truncGen T V hV) t x - T.stoneU t x‖ ≤ ‖truncDefect T V hV‖ * ‖x‖ * t
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le
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

theorem BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : x ∈ V) :
    ‖flow (truncGen T V hV) t x - T.stoneU t x‖ ≤ ‖truncDefect T V hV‖ * ‖x‖ * t := by sorry
