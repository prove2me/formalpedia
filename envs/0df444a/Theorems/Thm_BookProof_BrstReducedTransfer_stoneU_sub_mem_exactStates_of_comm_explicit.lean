-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_stoneU_sub_mem_exactStates_of_comm_explicit
-- name    : BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_of_comm_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:43.736661+00:00
-- url     : https://prove2.me/theorems/2b7d8cee-bc38-4e24-9411-bcb1d9b30431
-- title:
--   A commuting Stone flow preserves exact-state equivalence
-- statement:
--   If the Stone flow of $T$ commutes with the gauge projection, then two vectors whose difference is an exact state continue to differ by an exact state after evolution: from $x - y \in \mathrm{exactStates}$ follows $\mathrm{stoneU}_t x - \mathrm{stoneU}_t y \in \mathrm{exactStates}$ for every $t$.
--
--   Exact states are the pure-gauge directions; the statement says the flow is well defined on the quotient by them, which is the technical heart of the BRST reduction: physical observables are functions on that quotient, so the evolution has to descend to it.
--
--   Corrected statement of the retired node `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates`, with the commutation hypothesis explicit in the binder list.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterBrstReducedTransfer.lean

-- Corrected statement of BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates.
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

theorem BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_of_comm_explicit (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y)) (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) : T.stoneU t x - T.stoneU t y ∈ exactStates Om := by sorry
