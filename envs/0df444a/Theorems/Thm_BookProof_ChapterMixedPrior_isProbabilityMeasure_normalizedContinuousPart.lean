-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_isProbabilityMeasure_normalizedContinuousPart
-- name    : BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:10:18.89215+00:00
-- url     : https://prove2.me/theorems/c99ad6d0-1a59-4e52-b854-04fbd6a35e95
-- title:
--   `BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart` (mu : Measure X) [IsFiniteMeasure mu] (h : ¬ IsPurelyAtomic mu) : IsProbabilityMeasure (normalizedContin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart` (mu : Measure X) [IsFiniteMeasure mu] (h : ¬ IsPurelyAtomic mu) : IsProbabilityMeasure (normalizedContinuousPart mu)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.isProbabilityMeasure_normalizedContinuousPart (mu : Measure X)
    [IsFiniteMeasure mu] (h : ¬ IsPurelyAtomic mu) :
    IsProbabilityMeasure (normalizedContinuousPart mu) := by sorry
