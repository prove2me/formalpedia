-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_qgProd_ae_inv_prime
-- name    : BookProof.QgMultiHalfDensity.qgProd_ae_inv_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:33:47.051993+00:00
-- url     : https://prove2.me/theorems/7c526348-2aa6-4b17-86f3-7623fefac534
-- title:
--   BookProof.QgMultiHalfDensity.qgProd_ae_inv'
-- statement:
--   BookProof.QgMultiHalfDensity.qgProd_ae_inv'

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.qgProd_ae_inv'
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

theorem BookProof.QgMultiHalfDensity.qgProd_ae_inv_prime :
    ∀ᵐ p ∂(BookProof.ScalaronDensitized.physMeasure.prod mu),
      qgProdSquare (qgProdSqrt p) = p := by sorry
