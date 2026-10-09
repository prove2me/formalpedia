-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_ham_eq_toLp
-- name    : BookProof.ScalaronFiberFL.ham_eq_toLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:03:02.654574+00:00
-- url     : https://prove2.me/theorems/536e966f-8ec4-4c6b-b8f4-1dafc3eb5511
-- title:
--   The Lean 4 theorem `ham_eq_toLp` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ScalaronFiberFL.ham_eq_toLp` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.ham_eq_toLp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.StrichartzWave
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

theorem BookProof.ScalaronFiberFL.ham_eq_toLp (W : WallPot) (s : ℝ) (f : ccSchwartz ℝ) :
    W.ham s (ccEquiv ℝ f) = (hamS W s f).toLp 2 (volume : Measure ℝ) := by sorry
