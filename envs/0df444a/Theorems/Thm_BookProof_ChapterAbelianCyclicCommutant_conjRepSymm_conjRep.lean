-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRepSymm_conjRep
-- name    : BookProof.ChapterAbelianCyclicCommutant.conjRepSymm_conjRep
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:27.786151+00:00
-- url     : https://prove2.me/theorems/69076f30-7d7f-4af6-986f-ef952e312266
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.conjRepSymm_conjRep` (S : Lp ℂ 2 (repMeasure pi xi) →L[ℂ] Lp ℂ 2 (repMeasure pi xi)) : conjRepSymm pi xi hcyc (conjRep pi xi hcyc S) = S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.conjRepSymm_conjRep` (S : Lp ℂ 2 (repMeasure pi xi) →L[ℂ] Lp ℂ 2 (repMeasure pi xi)) : conjRepSymm pi xi hcyc (conjRep pi xi hcyc S) = S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.conjRepSymm_conjRep`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.conjRepSymm_conjRep
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

theorem BookProof.ChapterAbelianCyclicCommutant.conjRepSymm_conjRep (S : Lp ℂ 2 (repMeasure pi xi) →L[ℂ] Lp ℂ 2 (repMeasure pi xi)) :
    conjRepSymm pi xi hcyc (conjRep pi xi hcyc S) = S := by sorry
