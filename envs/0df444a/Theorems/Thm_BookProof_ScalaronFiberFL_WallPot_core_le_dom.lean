-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_core_le_dom
-- name    : BookProof.ScalaronFiberFL.WallPot.core_le_dom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T17:55:26.849916+00:00
-- url     : https://prove2.me/theorems/5f9dc551-6eff-4b4e-88ed-e6bb511617e3
-- title:
--   The Lean 4 theorem `core_le_dom` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `core_le_dom` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.WallPot.core_le_dom
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.QgOuterFockFL
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot



open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (W : WallPot) (s : ℝ)
variable (W : WallPot) (s : ℝ) (hs : 0 ≤ s)

theorem BookProof.ScalaronFiberFL.WallPot.core_le_dom : ccDomain ℝ ≤ (W.comparison s hs).dom := by sorry
