-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_noAtoms_normalizedContinuousPart
-- name    : BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:09:35.280683+00:00
-- url     : https://prove2.me/theorems/6a2dada1-cc0f-40f0-9618-63ada1b2691e
-- title:
--   `BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart` (mu : Measure X) [SFinite mu] : NullSingletonClass (normalizedContinuousPart mu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart` (mu : Measure X) [SFinite mu] : NullSingletonClass (normalizedContinuousPart mu)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart (mu : Measure X) [SFinite mu] :
    NullSingletonClass (normalizedContinuousPart mu) := by sorry
