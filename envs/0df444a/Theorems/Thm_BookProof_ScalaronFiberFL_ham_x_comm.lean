-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_ham_x_comm
-- name    : BookProof.ScalaronFiberFL.ham_x_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:04:05.686987+00:00
-- url     : https://prove2.me/theorems/c4c3cb05-ddc4-465d-9e47-f64fdad94787
-- title:
--   The Lean 4 theorem `ham_x_comm` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ScalaronFiberFL.ham_x_comm` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.ham_x_comm
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

theorem BookProof.ScalaronFiberFL.ham_x_comm (W : WallPot) (s : ℝ) (f g : ccSchwartz ℝ) :
    (starRingEnd ℂ) (inner ℂ (xCc (ccEquiv ℝ g)) (W.ham s (ccEquiv ℝ f)) : ℂ)
      - (inner ℂ (xCc (ccEquiv ℝ f)) (W.ham s (ccEquiv ℝ g)) : ℂ)
      = -2 * (inner ℂ ((ccEquiv ℝ f : ccDomain ℝ) : L2R) (derivL2 g) : ℂ) := by sorry
