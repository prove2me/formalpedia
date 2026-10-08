-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_multiHalfDensityUnitary_symm_apply
-- name    : BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_symm_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:37:41.99515+00:00
-- url     : https://prove2.me/theorems/1d7da67a-637b-4d79-9a7e-a61673b81ef7
-- title:
--   `BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_symm_apply` (h : Lp ℂ 2 (qgSrcMeasure.prod mu)) : ((multiHalfDensityUnitary mu).symm h : ℝ × X → ℂ) =ᵐ[BookProof.ScalaronDensi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_symm_apply` (h : Lp ℂ 2 (qgSrcMeasure.prod mu)) : ((multiHalfDensityUnitary mu).symm h : ℝ × X → ℂ) =ᵐ[BookProof.ScalaronDensitized.physMeasure.prod mu] fun p => (h : ℝ × X → ℂ) (Real.sqrt p.1, p.2)
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_symm_apply`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_symm_apply
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

theorem BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_symm_apply (h : Lp ℂ 2 (qgSrcMeasure.prod mu)) :
    ((multiHalfDensityUnitary mu).symm h : ℝ × X → ℂ)
      =ᵐ[BookProof.ScalaronDensitized.physMeasure.prod mu]
        fun p => (h : ℝ × X → ℂ) (Real.sqrt p.1, p.2) := by sorry
