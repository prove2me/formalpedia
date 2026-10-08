-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDecomposition_probability_measure_five_types
-- name    : BookProof.ChapterAtomicDecomposition.probability_measure_five_types
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:54:37.597443+00:00
-- url     : https://prove2.me/theorems/dd8dc9ed-facc-4889-b103-0f092cfd3abc
-- title:
--   `BookProof.ChapterAtomicDecomposition.probability_measure_five_types` (mu : Measure X) [IsProbabilityMeasure mu] : (continuousPart mu = 0 ∧ (atoms mu).Finite ∧ (atoms mu).Nonempty)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDecomposition`.
--
--   `BookProof.ChapterAtomicDecomposition.probability_measure_five_types` (mu : Measure X) [IsProbabilityMeasure mu] : (continuousPart mu = 0 ∧ (atoms mu).Finite ∧ (atoms mu).Nonempty) ∨ (continuousPart mu = 0 ∧ (atoms mu).Infinite) ∨ (continuousPart mu ≠ 0 ∧ atoms mu = ∅) ∨ (continuousPart mu ≠ 0 ∧ (atoms mu).Finite ∧ (atoms mu).Nonempty) ∨ (continuousPart mu ≠ 0 ∧ (atoms mu).Infinite)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDecomposition.probability_measure_five_types`.

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.probability_measure_five_types
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterAtomicDecomposition.probability_measure_five_types (mu : Measure X) [IsProbabilityMeasure mu] :
    (continuousPart mu = 0 ∧ (atoms mu).Finite ∧ (atoms mu).Nonempty) ∨
    (continuousPart mu = 0 ∧ (atoms mu).Infinite) ∨
    (continuousPart mu ≠ 0 ∧ atoms mu = ∅) ∨
    (continuousPart mu ≠ 0 ∧ (atoms mu).Finite ∧ (atoms mu).Nonempty) ∨
    (continuousPart mu ≠ 0 ∧ (atoms mu).Infinite) := by sorry
