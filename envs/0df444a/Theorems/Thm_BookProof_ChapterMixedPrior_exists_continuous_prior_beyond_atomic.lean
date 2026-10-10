-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_exists_continuous_prior_beyond_atomic
-- name    : BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:09:35.377967+00:00
-- url     : https://prove2.me/theorems/fdf70108-4ed5-40f7-b4e4-700109a4b555
-- title:
--   `BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic` (mu : Measure X) [IsProbabilityMeasure mu] (h : ¬ IsPurelyAtomic mu) : ∃ nu : Measure X, IsProbabilityMeasure nu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic` (mu : Measure X) [IsProbabilityMeasure mu] (h : ¬ IsPurelyAtomic mu) : ∃ nu : Measure X, IsProbabilityMeasure nu ∧ NullSingletonClass nu ∧ ¬ IsPurelyAtomic nu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic
import Definitions.Def_ChapterAtomicDecomposition
import Mathlib
import Definitions.Def_ChapterMixedPrior
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic (mu : Measure X) [IsProbabilityMeasure mu]
    (h : ¬ IsPurelyAtomic mu) :
    ∃ nu : Measure X, IsProbabilityMeasure nu ∧ NullSingletonClass nu ∧ ¬ IsPurelyAtomic nu := by sorry
