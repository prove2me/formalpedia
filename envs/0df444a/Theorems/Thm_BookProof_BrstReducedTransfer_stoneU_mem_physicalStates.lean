-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_stoneU_mem_physicalStates
-- name    : BookProof.BrstReducedTransfer.stoneU_mem_physicalStates
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:11:49.029974+00:00
-- url     : https://prove2.me/theorems/80211606-bf94-4657-8128-01b4f24770e5
-- title:
--   `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates` (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) : T.stoneU t x ∈ physicalStates Om
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates` (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) : T.stoneU t x ∈ physicalStates Om
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.stoneU_mem_physicalStates
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

theorem BookProof.BrstReducedTransfer.stoneU_mem_physicalStates (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) :
    T.stoneU t x ∈ physicalStates Om := by sorry
