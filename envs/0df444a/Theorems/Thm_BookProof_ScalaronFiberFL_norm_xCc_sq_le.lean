-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_norm_xCc_sq_le
-- name    : BookProof.ScalaronFiberFL.norm_xCc_sq_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T18:02:10.276132+00:00
-- url     : https://prove2.me/theorems/0c90ad80-ba23-4509-9c24-1230a2c49c31
-- title:
--   The Lean 4 theorem `norm_xCc_sq_le` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_xCc_sq_le` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.norm_xCc_sq_le
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
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.ScalaronFiberFL.norm_xCc_sq_le (W : WallPot) (s : ℝ) (hs : 0 ≤ s) (f : ccSchwartz ℝ) :
    ‖xCc (ccEquiv ℝ f)‖ ^ 2 ≤ 4 * quadForm (W.ham s) (ccEquiv ℝ f) := by sorry
