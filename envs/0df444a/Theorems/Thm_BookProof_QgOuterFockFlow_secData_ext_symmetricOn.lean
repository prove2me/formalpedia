-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFlow_secData_ext_symmetricOn
-- name    : BookProof.QgOuterFockFlow.secData_ext_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T10:18:19.111139+00:00
-- url     : https://prove2.me/theorems/64e2d999-f8ab-40b6-9bdf-407fb89d5a94
-- title:
--   The Lean 4 theorem `secData_ext_symmetricOn` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `secData_ext_symmetricOn` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockFlow.lean

-- Generated from ChapterQgOuterFockFlow.lean — theorem BookProof.QgOuterFockFlow.secData_ext_symmetricOn
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open Filter Topology
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato

noncomputable section

variable {ι : Type*} (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgOuterFockFlow.secData_ext_symmetricOn :
    SymmetricOn (secN W Q).dom (secData W Q).ext := by sorry
