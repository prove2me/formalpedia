-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_mem_of_proj
-- name    : BookProof.BrstUnboundedLeakage.flow_mem_of_proj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:19:45.812282+00:00
-- url     : https://prove2.me/theorems/0991533b-d661-417d-8262-6f692963e2e5
-- title:
--   `BookProof.BrstUnboundedLeakage.flow_mem_of_proj` {P B : H →L[ℂ] H} (hPB : P * B = B) (t : ℝ) {x : H} (hx : P x = x) : P (flow B t x) = flow B t x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.flow_mem_of_proj` {P B : H →L[ℂ] H} (hPB : P * B = B) (t : ℝ) {x : H} (hx : P x = x) : P (flow B t x) = flow B t x
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.flow_mem_of_proj`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.flow_mem_of_proj
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.flow_mem_of_proj {P B : H →L[ℂ] H} (hPB : P * B = B)
    (t : ℝ) {x : H} (hx : P x = x) : P (flow B t x) = flow B t x := by sorry
