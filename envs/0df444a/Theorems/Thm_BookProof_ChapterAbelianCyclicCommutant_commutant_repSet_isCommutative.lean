-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_commutant_repSet_isCommutative
-- name    : BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative
-- status  : Disproved
-- author  : @leonardopedro
-- created : 2026-10-17T01:50:18.413595+00:00
-- url     : https://prove2.me/theorems/6e43a454-1858-473f-b0d5-d3d75d3828bf
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative` {S R : H →L[ℂ] H} (hS : S ∈ (repSet pi).centralizer) (hR : R ∈ (repSet pi).centralizer) : S * R = R * S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative` {S R : H →L[ℂ] H} (hS : S ∈ (repSet pi).centralizer) (hR : R ∈ (repSet pi).centralizer) : S * R = R * S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative
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

theorem BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative {S R : H →L[ℂ] H}
    (hS : S ∈ (repSet pi).centralizer) (hR : R ∈ (repSet pi).centralizer) :
    S * R = R * S := by sorry
