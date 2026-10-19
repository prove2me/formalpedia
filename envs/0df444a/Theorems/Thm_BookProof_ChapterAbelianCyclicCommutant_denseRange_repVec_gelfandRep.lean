-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_denseRange_repVec_gelfandRep
-- name    : BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:49.349534+00:00
-- url     : https://prove2.me/theorems/3c2683d1-c68d-4a82-8695-d2118572e73f
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep` {rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {xi : H} (hcyc : DenseRange fun a : A => rho a xi) : DenseRange (repVec (gelfand
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep` {rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {xi : H} (hcyc : DenseRange fun a : A => rho a xi) : DenseRange (repVec (gelfandRep rho) xi)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralCommutant
import Definitions.Def_ChapterAbelianCyclicModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
open BookProof.ChapterAbelianCyclicCommutant


noncomputable section

open MeasureTheory Complex WeakDual


open BookProof.ChapterLinftyMultiplication BookProof.ChapterLinftyMaximalAbelian
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralCommutant
open BookProof.ChapterAbelianCyclicModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))

variable {A : Type*} [CommCStarAlgebra A]

theorem BookProof.ChapterAbelianCyclicCommutant.denseRange_repVec_gelfandRep {rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {xi : H}
    (hcyc : DenseRange fun a : A => rho a xi) :
    DenseRange (repVec (gelfandRep rho) xi) := by sorry
