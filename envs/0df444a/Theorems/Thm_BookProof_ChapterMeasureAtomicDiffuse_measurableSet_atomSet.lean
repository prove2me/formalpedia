-- Prove2me | Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_measurableSet_atomSet
-- name    : BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:01:37.991395+00:00
-- url     : https://prove2.me/theorems/da0147ed-dbcd-463a-beef-d65dd1f3bbc0
-- title:
--   `BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet` [IsFiniteMeasure mu] : MeasurableSet (atomSet mu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasureAtomicDiffuse`.
--
--   `BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet` [IsFiniteMeasure mu] : MeasurableSet (atomSet mu)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet`.

-- Generated from ChapterMeasureAtomicDiffuse.lean — theorem BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse


noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

theorem BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet [IsFiniteMeasure mu] : MeasurableSet (atomSet mu) := by sorry
