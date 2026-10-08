-- Prove2me | Theorems.Thm_BookProof_ChapterAtomicDecomposition_measurableSet_atoms
-- name    : BookProof.ChapterAtomicDecomposition.measurableSet_atoms
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:52:09.74598+00:00
-- url     : https://prove2.me/theorems/1b42d513-674c-46a8-88c3-3b67e46ed2ae
-- title:
--   `BookProof.ChapterAtomicDecomposition.measurableSet_atoms` (mu : Measure X) [SFinite mu] : MeasurableSet (atoms mu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAtomicDecomposition`.
--
--   `BookProof.ChapterAtomicDecomposition.measurableSet_atoms` (mu : Measure X) [SFinite mu] : MeasurableSet (atoms mu)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAtomicDecomposition.measurableSet_atoms`.

-- Generated from ChapterAtomicDecomposition.lean — theorem BookProof.ChapterAtomicDecomposition.measurableSet_atoms
import Mathlib
import Definitions.Def_ChapterAtomicDecomposition
open BookProof.ChapterAtomicDecomposition


open MeasureTheory


variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem BookProof.ChapterAtomicDecomposition.measurableSet_atoms (mu : Measure X) [SFinite mu] : MeasurableSet (atoms mu) := by sorry
