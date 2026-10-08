-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_multiHalfDensityUnitary_apply
-- name    : BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:37:18.803987+00:00
-- url     : https://prove2.me/theorems/74dc7cf9-4484-452c-89a8-a66450e7082b
-- title:
--   `BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply` (g : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod mu)) : (multiHalfDensityUnitary mu g : ℝ × X → ℂ) =ᵐ[qgSrcMe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply` (g : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod mu)) : (multiHalfDensityUnitary mu g : ℝ × X → ℂ) =ᵐ[qgSrcMeasure.prod mu] fun p => (g : ℝ × X → ℂ) (p.1 ^ 2, p.2)
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply
import Definitions.Def_ChapterNavierStokesFockContinuum
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterScalaronDensitizedTransfer
open BookProof.QuantumGravityHalfDensity
open BookProof.ScalaronDensitized
open BookProof.QgMultiHalfDensity



open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}
variable {g : Y → ℝ}
variable {X : Type*} [MeasurableSpace X] (mu : Measure X)
variable [SFinite mu]

theorem BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply
    (g : Lp ℂ 2 (BookProof.ScalaronDensitized.physMeasure.prod mu)) :
    (multiHalfDensityUnitary mu g : ℝ × X → ℂ)
      =ᵐ[qgSrcMeasure.prod mu] fun p => (g : ℝ × X → ℂ) (p.1 ^ 2, p.2) := by sorry
