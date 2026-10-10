-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_physConfOp_quadForm_ge
-- name    : BookProof.ScalaronDensitized.physConfOp_quadForm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:22:06.227286+00:00
-- url     : https://prove2.me/theorems/6e8b14e8-369a-452e-acca-267223fc577f
-- title:
--   `BookProof.ScalaronDensitized.physConfOp_quadForm_ge` (halpha : 0 < alpha) (f : physConfCore M alpha) : -(M ^ 4 / (16 * alpha)) * ‖(f : Lp ℂ 2 physMeasure)‖ ^ 2 ≤ quadForm ((physCo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.physConfOp_quadForm_ge` (halpha : 0 < alpha) (f : physConfCore M alpha) : -(M ^ 4 / (16 * alpha)) * ‖(f : Lp ℂ 2 physMeasure)‖ ^ 2 ≤ quadForm ((physConfCore M alpha).subtype.comp (physConfOp M alpha)) f
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.physConfOp_quadForm_ge`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.physConfOp_quadForm_ge
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)
variable {X : Type*} [MeasurableSpace X]

theorem BookProof.ScalaronDensitized.physConfOp_quadForm_ge (halpha : 0 < alpha) (f : physConfCore M alpha) :
    -(M ^ 4 / (16 * alpha)) * ‖(f : Lp ℂ 2 physMeasure)‖ ^ 2
      ≤ quadForm ((physConfCore M alpha).subtype.comp (physConfOp M alpha)) f := by sorry
