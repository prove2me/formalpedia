-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_infDist_exactStates_stoneU_eq
-- name    : BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:12:34.437981+00:00
-- url     : https://prove2.me/theorems/b2b3c4a4-b365-45b6-8998-10fdabfc66d1
-- title:
--   `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq` (t : ℝ) (x : H) : Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq` (t : ℝ) (x : H) : Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq
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

theorem BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq (t : ℝ) (x : H) :
    Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om) := by sorry
