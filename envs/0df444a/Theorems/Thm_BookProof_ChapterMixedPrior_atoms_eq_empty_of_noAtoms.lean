-- Prove2me | Theorems.Thm_BookProof_ChapterMixedPrior_atoms_eq_empty_of_noAtoms
-- name    : BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T13:10:04.192994+00:00
-- url     : https://prove2.me/theorems/290a55dd-3acc-4440-a0d7-39301de96da3
-- title:
--   `BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms` (mu : Measure X) [NullSingletonClass mu] : atoms mu = ∅
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMixedPrior`.
--
--   `BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms` (mu : Measure X) [NullSingletonClass mu] : atoms mu = ∅
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms`.

-- Generated from ChapterMixedPrior.lean — theorem BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms
import Mathlib
import Definitions.Def_ChapterMixedPrior
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition
open BookProof.ChapterMixedPrior


open MeasureTheory ProbabilityTheory


open BookProof.ChapterAtomicDecomposition

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterMixedPrior.atoms_eq_empty_of_noAtoms (mu : Measure X) [NullSingletonClass mu] : atoms mu = ∅ := by sorry
