-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_stoneU_mem_physicalStates_of_comm_explicit
-- name    : BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_of_comm_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:49.398058+00:00
-- url     : https://prove2.me/theorems/8c96ad79-2407-4bd9-a962-b3b24f9ee136
-- title:
--   A commuting Stone flow preserves the physical states
-- statement:
--   If the Stone flow of $T$ commutes with the gauge projection $\mathrm{Om}$, then it maps physical states to physical states: for every $t$ and every $x$ with $x \in \mathrm{physicalStates}$, also $\mathrm{stoneU}_t x \in \mathrm{physicalStates}$.
--
--   Physical states are those annihilated by the gauge projection; commuting with $\mathrm{Om}$ means the flow does not create gauge charge, so the gauge-invariant sector is invariant under the time evolution.  This is the hypothesis under which the reduced (BRST) dynamics is well defined on the physical Hilbert space.
--
--   Corrected statement of the retired node `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates`, which the export had stripped of the commutation hypothesis.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterBrstReducedTransfer.lean

-- Corrected statement of BookProof.BrstReducedTransfer.stoneU_mem_physicalStates.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterBrstReducedTransfer.lean (Lean 4.28) and timepiece331/BookProof/ChapterBrstReducedTransfer.lean (Lean 4.33.1).
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

theorem BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_of_comm_explicit (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y)) (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) : T.stoneU t x ∈ physicalStates Om := by sorry
