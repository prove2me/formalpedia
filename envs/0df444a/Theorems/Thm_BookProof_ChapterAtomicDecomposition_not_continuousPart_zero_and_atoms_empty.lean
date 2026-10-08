-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDecomposition_not_continuousPart_zero_and_atoms_empty
-- name    : BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:56:48.210496+00:00
-- url     : https://prove2.me/theorems/0c96387e-3ad2-44d5-a39d-7192fa8c8321
-- title:
--   `BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty` (mu : Measure X) [IsProbabilityMeasure mu] : ¬ (continuousPart mu = 0 ∧ atoms mu = ∅)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDecomposition`.
--
--   `BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty` (mu : Measure X) [IsProbabilityMeasure mu] : ¬ (continuousPart mu = 0 ∧ atoms mu = ∅)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty`.

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty (mu : Measure X) [IsProbabilityMeasure mu] :
    ¬ (continuousPart mu = 0 ∧ atoms mu = ∅) := by sorry
