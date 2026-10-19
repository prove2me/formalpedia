-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_infDist_exactStates_stoneU_eq_inc
-- name    : BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T18:45:44.244034+00:00
-- url     : https://prove2.me/theorems/73062bf0-cc7c-4498-a9dc-38a89ae408be
-- title:
--   `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc` (t : ℝ) (x : H) : Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc` (t : ℝ) (x : H) : Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc`.
--
--   Replaces the retired node `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq`, whose stored statement omitted the `hcomm` hypothesis binder (dropped `include`).

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc
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

theorem BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_inc (t : ℝ) (x : H) :
    Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om) := by sorry
