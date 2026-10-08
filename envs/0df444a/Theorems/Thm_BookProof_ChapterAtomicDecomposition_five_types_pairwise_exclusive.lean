-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDecomposition_five_types_pairwise_exclusive
-- name    : BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:53:38.252983+00:00
-- url     : https://prove2.me/theorems/486f4ba3-3d4b-40e6-8969-a4ee54691b98
-- title:
--   `BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive` (mu : Measure X) : ¬ ((atoms mu).Finite ∧ (atoms mu).Infinite) ∧ ¬ ((atoms mu = ∅) ∧ (atoms mu).Nonempty) ∧ ¬ (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDecomposition`.
--
--   `BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive` (mu : Measure X) : ¬ ((atoms mu).Finite ∧ (atoms mu).Infinite) ∧ ¬ ((atoms mu = ∅) ∧ (atoms mu).Nonempty) ∧ ¬ ((atoms mu = ∅) ∧ (atoms mu).Infinite) ∧ ¬ (continuousPart mu = 0 ∧ continuousPart mu ≠ 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive`.

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterAtomicDecomposition.five_types_pairwise_exclusive (mu : Measure X) :
    ¬ ((atoms mu).Finite ∧ (atoms mu).Infinite) ∧
      ¬ ((atoms mu = ∅) ∧ (atoms mu).Nonempty) ∧
      ¬ ((atoms mu = ∅) ∧ (atoms mu).Infinite) ∧
      ¬ (continuousPart mu = 0 ∧ continuousPart mu ≠ 0) := by sorry
