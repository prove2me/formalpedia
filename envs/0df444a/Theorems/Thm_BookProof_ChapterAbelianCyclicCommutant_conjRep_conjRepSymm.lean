-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRep_conjRepSymm
-- name    : BookProof.ChapterAbelianCyclicCommutant.conjRep_conjRepSymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:48:50.056224+00:00
-- url     : https://prove2.me/theorems/c62bb85b-aecf-4925-afee-a0c2c73e29ae
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.conjRep_conjRepSymm` (S : H →L[ℂ] H) : conjRep pi xi hcyc (conjRepSymm pi xi hcyc S) = S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.conjRep_conjRepSymm` (S : H →L[ℂ] H) : conjRep pi xi hcyc (conjRepSymm pi xi hcyc S) = S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.conjRep_conjRepSymm`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.conjRep_conjRepSymm
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

theorem BookProof.ChapterAbelianCyclicCommutant.conjRep_conjRepSymm (S : H →L[ℂ] H) :
    conjRep pi xi hcyc (conjRepSymm pi xi hcyc S) = S := by sorry
