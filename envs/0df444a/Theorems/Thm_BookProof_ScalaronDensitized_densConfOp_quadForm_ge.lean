-- Prove2me | Theorems.Thm_BookProof_ScalaronDensitized_densConfOp_quadForm_ge
-- name    : BookProof.ScalaronDensitized.densConfOp_quadForm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:22:10.349298+00:00
-- url     : https://prove2.me/theorems/bfd101f2-a9b4-4707-82f9-16d14782e260
-- title:
--   `BookProof.ScalaronDensitized.densConfOp_quadForm_ge` (halpha : 0 < alpha) (f : densConfCore M alpha) : -(M ^ 4 / (16 * alpha)) * ‖(f : Lp ℂ 2 qgSrcMeasure)‖ ^ 2 ≤ quadForm ((densC
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronDensitizedTransfer`.
--
--   `BookProof.ScalaronDensitized.densConfOp_quadForm_ge` (halpha : 0 < alpha) (f : densConfCore M alpha) : -(M ^ 4 / (16 * alpha)) * ‖(f : Lp ℂ 2 qgSrcMeasure)‖ ^ 2 ≤ quadForm ((densConfCore M alpha).subtype.comp (densConfOp M alpha)) f
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronDensitized.densConfOp_quadForm_ge`.

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.densConfOp_quadForm_ge
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QuantumGravityHalfDensity
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

theorem BookProof.ScalaronDensitized.densConfOp_quadForm_ge (halpha : 0 < alpha) (f : densConfCore M alpha) :
    -(M ^ 4 / (16 * alpha)) * ‖(f : Lp ℂ 2 qgSrcMeasure)‖ ^ 2
      ≤ quadForm ((densConfCore M alpha).subtype.comp (densConfOp M alpha)) f := by sorry
