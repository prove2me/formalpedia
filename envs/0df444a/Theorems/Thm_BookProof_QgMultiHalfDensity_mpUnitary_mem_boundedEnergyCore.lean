-- Prove2me | Theorems.Thm_BookProof_QgMultiHalfDensity_mpUnitary_mem_boundedEnergyCore
-- name    : BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:36:40.195011+00:00
-- url     : https://prove2.me/theorems/fb91c040-3bcd-4cff-a6f4-30fb4a3ff06d
-- title:
--   `BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (x : bou
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgMultiHalfDensity`.
--
--   `BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore` (hPhi : MeasurePreserving Phi mu nu) (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x) (x : boundedEnergyCore nu g) : mpUnitary hPhi hPsi hinv (x : Lp ℂ 2 nu) ∈ boundedEnergyCore mu (fun t => g (Phi t))
--
--   Formalization note: Lean 4 identifier `BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore`.

-- Generated from ChapterQgMultiHalfDensity.lean — theorem BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore
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

theorem BookProof.QgMultiHalfDensity.mpUnitary_mem_boundedEnergyCore (hPhi : MeasurePreserving Phi mu nu)
    (hPsi : MeasurePreserving Psi nu mu) (hinv : ∀ᵐ x ∂mu, Psi (Phi x) = x)
    (x : boundedEnergyCore nu g) :
    mpUnitary hPhi hPsi hinv (x : Lp ℂ 2 nu) ∈ boundedEnergyCore mu (fun t => g (Phi t)) := by sorry
