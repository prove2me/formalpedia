-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_stoneU_sub_mem_exactStates_inc
-- name    : BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T18:45:35.942775+00:00
-- url     : https://prove2.me/theorems/74834722-c593-4f88-a925-a7d0b7bf7463
-- title:
--   `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_inc` (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) : T.stoneU t x - T.stoneU t y ∈ exactStates Om
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_inc` (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) : T.stoneU t x - T.stoneU t y ∈ exactStates Om
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_inc`.
--
--   Replaces the retired node `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates`, whose stored statement omitted the `hcomm` hypothesis binder (dropped `include`).

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_inc
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent




variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →L[ℂ] H)
variable (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y))

include hcomm in

theorem BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_inc (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) :
    T.stoneU t x - T.stoneU t y ∈ exactStates Om := by sorry
