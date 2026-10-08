-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDecomposition_atoms_countable
-- name    : BookProof.ChapterAtomicDecomposition.atoms_countable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:53:47.086533+00:00
-- url     : https://prove2.me/theorems/93836f4a-12f5-4d29-a382-3c88b422e5cf
-- title:
--   `BookProof.ChapterAtomicDecomposition.atoms_countable` (mu : Measure X) [SFinite mu] : (atoms mu).Countable
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDecomposition`.
--
--   `BookProof.ChapterAtomicDecomposition.atoms_countable` (mu : Measure X) [SFinite mu] : (atoms mu).Countable
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDecomposition.atoms_countable`.

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.atoms_countable
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterAtomicDecomposition.atoms_countable (mu : Measure X) [SFinite mu] : (atoms mu).Countable := by sorry
