-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_boundedEnergyCore_surjective
-- name    : BookProof.QgMultiHalfDensity.mpUnitary_boundedEnergyCore_surjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:36:35.157981+00:00
-- url     : https://prove2.me/theorems/47292d32-2cb2-46b8-aeee-d87b57c264aa
-- title:
--   `BookProof.QgMultiHalfDensity.mpUnitary_boundedEnergyCore_surjective` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.mpUnitary_boundedEnergyCore_surjective` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (hinv' : ∀ᵐ y ∂nu, Phi (Psi y) = y) (h : boundedEnergyCore mu (fun t => g (Phi t))) : ∃ x : boundedEnergyCore nu g, mpUnitary hPhi hPsi hinv (x : Lp ℂ 2 nu) = (h : Lp ℂ 2 mu)
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.mpUnitary_boundedEnergyCore_surjective`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.mpUnitary_boundedEnergyCore_surjective
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
import Definitions.Def_ChapterNavierStokesFockContinuum
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QgMultiHalfDensity



open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}
variable {g : Y → ℝ}

theorem BookProof.QgMultiHalfDensity.mpUnitary_boundedEnergyCore_surjective (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x)
    (hinv' : ∀ᵐ y ∂nu, Phi (Psi y) = y)
    (h : boundedEnergyCore mu (fun t => g (Phi t))) :
    ∃ x : boundedEnergyCore nu g,
      mpUnitary hPhi hPsi hinv (x : Lp ℂ 2 nu) = (h : Lp ℂ 2 mu) := by sorry
