-- Prove2me | Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_countable_atomSet
-- name    : BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:01:47.842447+00:00
-- url     : https://prove2.me/theorems/8b12cb40-16a2-4d4e-81ca-9a7b7f08bc80
-- title:
--   `BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet` [IsFiniteMeasure mu] : (atomSet mu).Countable
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasureAtomicDiffuse`.
--
--   `BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet` [IsFiniteMeasure mu] : (atomSet mu).Countable
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet`.

-- Generated from ChapterMeasureAtomicDiffuse.lean — theorem BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse


noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

theorem BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet [IsFiniteMeasure mu] : (atomSet mu).Countable := by sorry
