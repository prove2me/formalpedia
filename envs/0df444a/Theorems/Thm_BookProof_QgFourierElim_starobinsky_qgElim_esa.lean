-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_starobinsky_qgElim_esa
-- name    : BookProof.QgFourierElim.starobinsky_qgElim_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T21:28:18.268287+00:00
-- url     : https://prove2.me/theorems/50da3b5b-c65c-460e-8891-a13441a5e984
-- title:
--   `BookProof.QgFourierElim.starobinsky_qgElim_esa` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : EssentiallySelfAdjointOn (secN (starobinskyWall M alpha halpha) (qgElimModes g)).dom (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.starobinsky_qgElim_esa` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : EssentiallySelfAdjointOn (secN (starobinskyWall M alpha halpha) (qgElimModes g)).dom (secData (starobinskyWall M alpha halpha) (qgElimModes g)).ext
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.starobinsky_qgElim_esa`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.starobinsky_qgElim_esa
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

theorem BookProof.QgFourierElim.starobinsky_qgElim_esa (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) :
    EssentiallySelfAdjointOn
        (secN (starobinskyWall M alpha halpha) (qgElimModes g)).dom
      (secData (starobinskyWall M alpha halpha) (qgElimModes g)).ext := by sorry
