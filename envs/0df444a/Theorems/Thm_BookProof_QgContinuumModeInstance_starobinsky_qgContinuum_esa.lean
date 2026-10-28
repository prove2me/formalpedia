-- Prove2me | Theorems.Thm_BookProof_QgContinuumModeInstance_starobinsky_qgContinuum_esa
-- name    : BookProof.QgContinuumModeInstance.starobinsky_qgContinuum_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:32:08.328847+00:00
-- url     : https://prove2.me/theorems/7d970b41-3db9-45e9-85f7-370f0c682939
-- title:
--   `BookProof.QgContinuumModeInstance.starobinsky_qgContinuum_esa` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : EssentiallySelfAdjointOn (secN (starobinskyWall M alpha halpha) (qgCont
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgContinuumModeInstance`.
--
--   `BookProof.QgContinuumModeInstance.starobinsky_qgContinuum_esa` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : EssentiallySelfAdjointOn (secN (starobinskyWall M alpha halpha) (qgContinuumModes g)).dom (secData (starobinskyWall M alpha halpha) (qgContinuumModes g)).ext
--
--   Formalization note: Lean 4 identifier `BookProof.QgContinuumModeInstance.starobinsky_qgContinuum_esa`.

-- Generated from ChapterQgContinuumModeInstance.lean — theorem BookProof.QgContinuumModeInstance.starobinsky_qgContinuum_esa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.QgContinuumModeInstance



open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

theorem BookProof.QgContinuumModeInstance.starobinsky_qgContinuum_esa (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) :
    EssentiallySelfAdjointOn
        (secN (starobinskyWall M alpha halpha) (qgContinuumModes g)).dom
      (secData (starobinskyWall M alpha halpha) (qgContinuumModes g)).ext := by sorry
