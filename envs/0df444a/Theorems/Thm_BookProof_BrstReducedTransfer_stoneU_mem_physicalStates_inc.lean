-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_stoneU_mem_physicalStates_inc
-- name    : BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T18:45:20.175964+00:00
-- url     : https://prove2.me/theorems/63ab6a3e-057c-4a30-ba16-acd92418e8a4
-- title:
--   `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc` (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) : T.stoneU t x ∈ physicalStates Om
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc` (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) : T.stoneU t x ∈ physicalStates Om
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc`.
--
--   Replaces the retired node `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates`, whose stored statement omitted the `hcomm` hypothesis binder (dropped `include`).

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc
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

theorem BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_inc (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) :
    T.stoneU t x ∈ physicalStates Om := by sorry
