-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_continuousPart_eq_zero_of_isPurelyAtomic
-- name    : BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:08:52.79563+00:00
-- url     : https://prove2.me/theorems/9f7ab6e4-7f31-431f-878d-5d40c9327082
-- title:
--   `BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic` {mu : Measure X} (h : IsPurelyAtomic mu) : continuousPart mu = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic` {mu : Measure X} (h : IsPurelyAtomic mu) : continuousPart mu = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.continuousPart_eq_zero_of_isPurelyAtomic {mu : Measure X} (h : IsPurelyAtomic mu) :
    continuousPart mu = 0 := by sorry
