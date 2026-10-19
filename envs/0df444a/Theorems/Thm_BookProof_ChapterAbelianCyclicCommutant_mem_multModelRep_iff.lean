-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_mem_multModelRep_iff
-- name    : BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:41.728845+00:00
-- url     : https://prove2.me/theorems/c9959517-ba55-4450-9edb-97739126bd7e
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff` (S : H →L[ℂ] H) : S ∈ multModelRep pi xi hcyc ↔ conjRepSymm pi xi hcyc S ∈ multAlgebra (repMeasure pi xi)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff` (S : H →L[ℂ] H) : S ∈ multModelRep pi xi hcyc ↔ conjRepSymm pi xi hcyc S ∈ multAlgebra (repMeasure pi xi)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff
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

theorem BookProof.ChapterAbelianCyclicCommutant.mem_multModelRep_iff (S : H →L[ℂ] H) :
    S ∈ multModelRep pi xi hcyc ↔
      conjRepSymm pi xi hcyc S ∈ multAlgebra (repMeasure pi xi) := by sorry
