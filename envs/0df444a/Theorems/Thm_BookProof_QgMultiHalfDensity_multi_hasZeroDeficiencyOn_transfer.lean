-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_multi_hasZeroDeficiencyOn_transfer
-- name    : BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:37:20.462153+00:00
-- url     : https://prove2.me/theorems/20002a03-7b25-4825-b25e-180282d554ab
-- title:
--   `BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer` {V : ℝ × X → ℝ} (hV : Measurable V) (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn (boundedEnergyCore (qg
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer` {V : ℝ × X → ℝ} (hV : Measurable V) (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn (boundedEnergyCore (qgSrcMeasure.prod mu) fun p => V (qgProdSquare p)) (multOp (qgSrcMeasure.prod mu) (hV.comp (measurePreserving_qgProdSquare mu).measurable))) : BookProof.NavierStokesFlow.HasZeroDeficiencyOn (boundedEnergyCore (BookProof.ScalaronDensitized.physMeasure.prod mu) V) (multOp (BookProof.ScalaronDensitized.physMeasure.prod mu) hV)
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterScalaronDensitizedTransfer
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
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

theorem BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer {V : ℝ × X → ℝ} (hV : Measurable V)
    (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (qgSrcMeasure.prod mu) fun p => V (qgProdSquare p))
      (multOp (qgSrcMeasure.prod mu) (hV.comp (measurePreserving_qgProdSquare mu).measurable))) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore (BookProof.ScalaronDensitized.physMeasure.prod mu) V)
      (multOp (BookProof.ScalaronDensitized.physMeasure.prod mu) hV) := by sorry
