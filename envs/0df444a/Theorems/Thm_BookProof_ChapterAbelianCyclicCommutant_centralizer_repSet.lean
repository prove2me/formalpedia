-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_centralizer_repSet
-- name    : BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:40.572164+00:00
-- url     : https://prove2.me/theorems/34d4daa9-c624-43a6-88ff-f0916866cd4b
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet` : (repSet pi).centralizer = multModelRep pi xi hcyc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet` : (repSet pi).centralizer = multModelRep pi xi hcyc
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralCommutant
import Definitions.Def_ChapterAbelianCyclicModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
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

theorem BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet : (repSet pi).centralizer = multModelRep pi xi hcyc := by sorry
