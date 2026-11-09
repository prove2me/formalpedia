-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFlow_secN_dom_dense
-- name    : BookProof.QgOuterFockFlow.secN_dom_dense
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T10:18:15.026227+00:00
-- url     : https://prove2.me/theorems/26ffffab-de49-4d1f-9a3a-e33fa549c2d4
-- title:
--   The Lean 4 theorem `secN_dom_dense` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `secN_dom_dense` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockFlow.lean

-- Generated from ChapterQgOuterFockFlow.lean — theorem BookProof.QgOuterFockFlow.secN_dom_dense
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
open Filter Topology
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato

noncomputable section

variable {ι : Type*} (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgOuterFockFlow.secN_dom_dense : Dense (((secN W Q).dom : Submodule ℂ (Sec ι)) : Set (Sec ι)) := by sorry
