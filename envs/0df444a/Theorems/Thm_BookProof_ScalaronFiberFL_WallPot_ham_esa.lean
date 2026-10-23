-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_ham_esa
-- name    : BookProof.ScalaronFiberFL.WallPot.ham_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T17:56:17.896555+00:00
-- url     : https://prove2.me/theorems/d805e3ad-f68f-4f99-b3e9-d6b54333c75b
-- title:
--   The Lean 4 theorem `ham_esa` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ham_esa` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.WallPot.ham_esa
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

theorem BookProof.ScalaronFiberFL.WallPot.ham_esa (hs : 0 ≤ s) : EssentiallySelfAdjointOn (ccDomain ℝ) (W.ham s) := by sorry
