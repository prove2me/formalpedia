-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_cc_integrable_sq
-- name    : BookProof.ScalaronFiberFL.cc_integrable_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T18:01:01.488619+00:00
-- url     : https://prove2.me/theorems/ebd06060-211f-49a8-97e5-57af0b96c33a
-- title:
--   The Lean 4 theorem `cc_integrable_sq` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cc_integrable_sq` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.cc_integrable_sq
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL



open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (W : WallPot) (s : ℝ)

theorem BookProof.ScalaronFiberFL.cc_integrable_sq (f : ccSchwartz ℝ) :
    Integrable fun x => ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by sorry
