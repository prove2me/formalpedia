-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_exists_atom_of_isPurelyAtomic
-- name    : BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:09:38.179668+00:00
-- url     : https://prove2.me/theorems/33f6322a-daf8-4602-bc2c-8f19a9560530
-- title:
--   `BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic` (mu : Measure X) [IsProbabilityMeasure mu] (h : IsPurelyAtomic mu) : (atoms mu).Nonempty
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic` (mu : Measure X) [IsProbabilityMeasure mu] (h : IsPurelyAtomic mu) : (atoms mu).Nonempty
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.exists_atom_of_isPurelyAtomic (mu : Measure X) [IsProbabilityMeasure mu]
    (h : IsPurelyAtomic mu) : (atoms mu).Nonempty := by sorry
