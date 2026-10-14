-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_symm_apply
-- name    : BookProof.QgMultiHalfDensity.mpUnitary_symm_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:17.504986+00:00
-- url     : https://prove2.me/theorems/ad6eeef6-414b-4341-8eb9-18bf98b17b00
-- title:
--   `BookProof.QgMultiHalfDensity.mpUnitary_symm_apply` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) : (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.mpUnitary_symm_apply` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) : ((mpUnitary hPhi hPsi hinv).symm h : Y → ℂ) =ᵐ[nu] fun y => (h : X → ℂ) (Psi y)
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.mpUnitary_symm_apply`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.mpUnitary_symm_apply
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

theorem BookProof.QgMultiHalfDensity.mpUnitary_symm_apply (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) :
    ((mpUnitary hPhi hPsi hinv).symm h : Y → ℂ) =ᵐ[nu] fun y => (h : X → ℂ) (Psi y) := by sorry
