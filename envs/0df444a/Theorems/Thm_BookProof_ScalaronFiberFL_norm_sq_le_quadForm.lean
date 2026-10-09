-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_norm_sq_le_quadForm
-- name    : BookProof.ScalaronFiberFL.norm_sq_le_quadForm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:03:59.131128+00:00
-- url     : https://prove2.me/theorems/70adf3e4-0e7d-476d-b9a5-1655dbe851b6
-- title:
--   The Lean 4 theorem `norm_sq_le_quadForm` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ScalaronFiberFL.norm_sq_le_quadForm` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.norm_sq_le_quadForm
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

theorem BookProof.ScalaronFiberFL.norm_sq_le_quadForm (W : WallPot) (s : ℝ) (hs : 1 ≤ s) (f : ccSchwartz ℝ) :
    ‖((ccEquiv ℝ f : ccDomain ℝ) : L2R)‖ ^ 2 ≤ quadForm (W.ham s) (ccEquiv ℝ f) := by sorry
