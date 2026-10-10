-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_symm_eq
-- name    : BookProof.QgMultiHalfDensity.mpUnitary_symm_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:41:33.474532+00:00
-- url     : https://prove2.me/theorems/abb8cd22-1057-4d94-9757-d69ff5ed26fb
-- title:
--   `BookProof.QgMultiHalfDensity.mpUnitary_symm_eq` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) : (mpU
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.mpUnitary_symm_eq` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) : (mpUnitary hPhi hPsi hinv).symm h = mpIsom hPsi h
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.mpUnitary_symm_eq`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.mpUnitary_symm_eq
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

theorem BookProof.QgMultiHalfDensity.mpUnitary_symm_eq (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (h : Lp ℂ 2 mu) :
    (mpUnitary hPhi hPsi hinv).symm h = mpIsom hPsi h := by sorry
