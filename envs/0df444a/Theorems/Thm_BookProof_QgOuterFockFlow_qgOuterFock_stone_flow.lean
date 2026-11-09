-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFlow_qgOuterFock_stone_flow
-- name    : BookProof.QgOuterFockFlow.qgOuterFock_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T10:21:15.172942+00:00
-- url     : https://prove2.me/theorems/4374cd33-f992-42fd-8c32-5465b56f11e4
-- title:
--   The Lean 4 theorem `qgOuterFock_stone_flow` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgOuterFock_stone_flow` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockFlow.lean

-- Generated from ChapterQgOuterFockFlow.lean — theorem BookProof.QgOuterFockFlow.qgOuterFock_stone_flow
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.StoneBridge
open Filter Topology
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato

noncomputable section

variable {ι : Type*} (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgOuterFockFlow.qgOuterFock_stone_flow :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (U : ℝ → (Sec ι →L[ℂ] Sec ι)),
      IsSelfAdjointExtension (secData W Q).ext T.op ∧ IsStoneFlow T U := by sorry
