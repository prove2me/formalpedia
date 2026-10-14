-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_apply
-- name    : BookProof.QgMultiHalfDensity.mpUnitary_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:40.029334+00:00
-- url     : https://prove2.me/theorems/add40861-87f4-4149-8317-38b77bf777c7
-- title:
--   `BookProof.QgMultiHalfDensity.mpUnitary_apply` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (g : Lp ℂ 2 nu) : (mpUni
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.mpUnitary_apply` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (g : Lp ℂ 2 nu) : (mpUnitary hPhi hPsi hinv g : X → ℂ) =ᵐ[mu] fun x => (g : Y → ℂ) (Phi x)
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.mpUnitary_apply`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.mpUnitary_apply
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Mathlib
import Definitions.Def_ChapterQgMultiHalfDensity
open BookProof.QgMultiHalfDensity



open MeasureTheory Set
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.QuantumGravityHalfDensity

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {Phi : X → Y} {Psi : Y → X}

theorem BookProof.QgMultiHalfDensity.mpUnitary_apply (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (g : Lp ℂ 2 nu) :
    (mpUnitary hPhi hPsi hinv g : X → ℂ) =ᵐ[mu] fun x => (g : Y → ℂ) (Phi x) := by sorry
