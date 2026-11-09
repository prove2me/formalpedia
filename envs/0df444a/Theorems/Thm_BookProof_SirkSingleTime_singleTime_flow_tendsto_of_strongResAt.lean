-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_singleTime_flow_tendsto_of_strongResAt
-- name    : BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-31T12:36:34.553854+00:00
-- url     : https://prove2.me/theorems/5d457c42-c115-4888-bdd9-19881b7266c9
-- title:
--   `BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt` {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) (v : E) (t : ℝ) : Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.sto
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt` {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) (v : E) (t : ℝ) : Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.SirkSingleTime


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

theorem BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt {l : ℝ} (hl : l ≠ 0)
    (h : StrongResAt T S l) (v : E) (t : ℝ) :
    Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
