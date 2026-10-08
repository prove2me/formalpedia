-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_truncGen_isSelfAdjoint
-- name    : BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:19:47.405589+00:00
-- url     : https://prove2.me/theorems/4490ab9d-7196-4182-a394-a28dce696244
-- title:
--   `BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint` : IsSelfAdjoint (truncGen T V hV)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint` : IsSelfAdjoint (truncGen T V hV)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
open BookProof.BrstLeakage
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint : IsSelfAdjoint (truncGen T V hV) := by sorry
