-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_hasZeroDeficiencyOn_transfer
-- name    : BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:37:02.372066+00:00
-- url     : https://prove2.me/theorems/5f483d98-536d-48bf-8bde-353cd4792749
-- title:
--   `BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (hinv' : ∀ᵐ y ∂nu, Phi (Psi y) = y) (hg : Measurable g) (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn (boundedEnergyCore mu (fun t => g (Phi t))) (multOp mu (hg.comp hPhi.measurable))) : BookProof.NavierStokesFlow.HasZeroDeficiencyOn (boundedEnergyCore nu g) (multOp nu hg)
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QgMultiHalfDensity



open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}
variable {g : Y → ℝ}

theorem BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x)
    (hinv' : ∀ᵐ y ∂nu, Phi (Psi y) = y) (hg : Measurable g)
    (hflat : BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore mu (fun t => g (Phi t))) (multOp mu (hg.comp hPhi.measurable))) :
    BookProof.NavierStokesFlow.HasZeroDeficiencyOn
      (boundedEnergyCore nu g) (multOp nu hg) := by sorry
