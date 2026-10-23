-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_WallPot_comparison_core
-- name    : BookProof.ScalaronFiberFL.WallPot.comparison_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T17:54:12.674978+00:00
-- url     : https://prove2.me/theorems/e6f34332-aecc-4590-b679-d705e23aaad7
-- title:
--   The Lean 4 theorem `comparison_core` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `comparison_core` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.WallPot.comparison_core
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

theorem BookProof.ScalaronFiberFL.WallPot.comparison_core (p : ccDomain ℝ) (h : (p : L2R) ∈ (W.comparison s hs).dom) :
    (W.comparison s hs).op ⟨(p : L2R), h⟩ = W.ham s p := by sorry
