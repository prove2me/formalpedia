-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_stoneU_sub_mem_exactStates
-- name    : BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:12:09.694975+00:00
-- url     : https://prove2.me/theorems/c12a92c5-a448-487a-8dc5-7f799cdab7ba
-- title:
--   `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates` (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) : T.stoneU t x - T.stoneU t y ∈ exactStates Om
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates` (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) : T.stoneU t x - T.stoneU t y ∈ exactStates Om
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →L[ℂ] H)
variable (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y))

theorem BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) :
    T.stoneU t x - T.stoneU t y ∈ exactStates Om := by sorry
