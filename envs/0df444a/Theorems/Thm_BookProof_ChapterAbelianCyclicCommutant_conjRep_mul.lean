-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_conjRep_mul
-- name    : BookProof.ChapterAbelianCyclicCommutant.conjRep_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:10.055058+00:00
-- url     : https://prove2.me/theorems/7d606581-8cd5-4713-91ab-0900cf3d5366
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.conjRep_mul` (A B : Lp ℂ 2 (repMeasure pi xi) →L[ℂ] Lp ℂ 2 (repMeasure pi xi)) : conjRep pi xi hcyc (A * B) = conjRep pi xi hcyc A * conjRe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.conjRep_mul` (A B : Lp ℂ 2 (repMeasure pi xi) →L[ℂ] Lp ℂ 2 (repMeasure pi xi)) : conjRep pi xi hcyc (A * B) = conjRep pi xi hcyc A * conjRep pi xi hcyc B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.conjRep_mul`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.conjRep_mul
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

theorem BookProof.ChapterAbelianCyclicCommutant.conjRep_mul (A B : Lp ℂ 2 (repMeasure pi xi) →L[ℂ] Lp ℂ 2 (repMeasure pi xi)) :
    conjRep pi xi hcyc (A * B) = conjRep pi xi hcyc A * conjRep pi xi hcyc B := by sorry
