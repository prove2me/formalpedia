-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_eq_zero_of_noAtoms_of_isPurelyAtomic
-- name    : BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:08:52.479983+00:00
-- url     : https://prove2.me/theorems/d460238c-1071-40f5-b557-ef67ac617ce6
-- title:
--   `BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic` (mu : Measure X) [NullSingletonClass mu] (h : IsPurelyAtomic mu) : mu = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic` (mu : Measure X) [NullSingletonClass mu] (h : IsPurelyAtomic mu) : mu = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.eq_zero_of_noAtoms_of_isPurelyAtomic (mu : Measure X) [NullSingletonClass mu]
    (h : IsPurelyAtomic mu) : mu = 0 := by sorry
