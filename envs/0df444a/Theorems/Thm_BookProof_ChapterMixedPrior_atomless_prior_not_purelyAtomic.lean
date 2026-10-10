-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_atomless_prior_not_purelyAtomic
-- name    : BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:08:59.967149+00:00
-- url     : https://prove2.me/theorems/84019c7a-a91a-4e0e-9025-fbecac3cc949
-- title:
--   `BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic` (mu : Measure X) [IsProbabilityMeasure mu] [NullSingletonClass mu] : ¬ IsPurelyAtomic mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic` (mu : Measure X) [IsProbabilityMeasure mu] [NullSingletonClass mu] : ¬ IsPurelyAtomic mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic
import Definitions.Def_ChapterAtomicDecomposition
import Mathlib
import Definitions.Def_ChapterMixedPrior
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic (mu : Measure X) [IsProbabilityMeasure mu]
    [NullSingletonClass mu] : ¬ IsPurelyAtomic mu := by sorry
