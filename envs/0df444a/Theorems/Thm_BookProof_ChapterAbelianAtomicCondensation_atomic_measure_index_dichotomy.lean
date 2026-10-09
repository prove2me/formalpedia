-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_atomic_measure_index_dichotomy
-- name    : BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:17:52.061069+00:00
-- url     : https://prove2.me/theorems/5edbf674-d604-401c-8de0-a79766ef8bbc
-- title:
--   `BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy` {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (mu : Measure X) [IsProbabilityMeasure mu]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianAtomicCondensation`.
--
--   `BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy` {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (mu : Measure X) [IsProbabilityMeasure mu] : (∃ n : ℕ, Nonempty (atoms mu ≃ Fin n)) ∨ Nonempty (atoms mu ≃ ℕ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy`.

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy
import Definitions.Def_ChapterAbelianDiagonalCountable
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable
open MeasureTheory

theorem BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (mu : Measure X) [IsProbabilityMeasure mu] :
    (∃ n : ℕ, Nonempty (atoms mu ≃ Fin n)) ∨ Nonempty (atoms mu ≃ ℕ) := by sorry
