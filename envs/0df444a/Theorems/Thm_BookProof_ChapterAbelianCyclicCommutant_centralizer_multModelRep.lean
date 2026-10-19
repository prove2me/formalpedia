-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_centralizer_multModelRep
-- name    : BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:47.347292+00:00
-- url     : https://prove2.me/theorems/9ac2a80c-0cc7-4fd2-9ab3-f52b3d3b23b0
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep` : (multModelRep pi xi hcyc).centralizer = multModelRep pi xi hcyc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep` : (multModelRep pi xi hcyc).centralizer = multModelRep pi xi hcyc
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep
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

theorem BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep :
    (multModelRep pi xi hcyc).centralizer = multModelRep pi xi hcyc := by sorry
