-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFlow_starobinsky_qgContinuum_stone_flow
-- name    : BookProof.QgOuterFockFlow.starobinsky_qgContinuum_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T10:18:51.683118+00:00
-- url     : https://prove2.me/theorems/e5f42354-e942-4111-99c3-8b2df09e14c9
-- title:
--   The Lean 4 theorem `starobinsky_qgContinuum_stone_flow` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinsky_qgContinuum_stone_flow` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockFlow.lean

-- Generated from ChapterQgOuterFockFlow.lean — theorem BookProof.QgOuterFockFlow.starobinsky_qgContinuum_stone_flow
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

theorem BookProof.QgOuterFockFlow.starobinsky_qgContinuum_stone_flow (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (U : ℝ → (Sec CMode →L[ℂ] Sec CMode)),
      IsSelfAdjointExtension (secData (starobinskyWall M alpha halpha)
          (qgContinuumModes g)).ext T.op ∧ IsStoneFlow T U := by sorry
