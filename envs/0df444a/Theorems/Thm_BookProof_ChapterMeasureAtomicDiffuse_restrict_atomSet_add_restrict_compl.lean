-- Prove2me | Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_restrict_atomSet_add_restrict_compl
-- name    : BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:01:57.227305+00:00
-- url     : https://prove2.me/theorems/160a6f34-226b-46d0-831a-988028b27449
-- title:
--   `BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl` [IsFiniteMeasure mu] : mu.restrict (atomSet mu) + mu.restrict (atomSet mu)ᶜ = mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasureAtomicDiffuse`.
--
--   `BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl` [IsFiniteMeasure mu] : mu.restrict (atomSet mu) + mu.restrict (atomSet mu)ᶜ = mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl`.

-- Generated from ChapterMeasureAtomicDiffuse.lean — theorem BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse


noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

theorem BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl [IsFiniteMeasure mu] :
    mu.restrict (atomSet mu) + mu.restrict (atomSet mu)ᶜ = mu := by sorry
