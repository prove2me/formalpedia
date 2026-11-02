-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_qgElim_esa
-- name    : BookProof.QgFourierElim.qgElim_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T21:28:03.978023+00:00
-- url     : https://prove2.me/theorems/3718003d-b525-4f39-b544-07cc08e40d87
-- title:
--   `BookProof.QgFourierElim.qgElim_esa` (W : WallPot) (g : ℝ) : EssentiallySelfAdjointOn (secN W (qgElimModes g)).dom (secData W (qgElimModes g)).ext
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.qgElim_esa` (W : WallPot) (g : ℝ) : EssentiallySelfAdjointOn (secN W (qgElimModes g)).dom (secData W (qgElimModes g)).ext
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.qgElim_esa`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.qgElim_esa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData



open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

theorem BookProof.QgFourierElim.qgElim_esa (W : WallPot) (g : ℝ) :
    EssentiallySelfAdjointOn (secN W (qgElimModes g)).dom (secData W (qgElimModes g)).ext := by sorry
