-- Prove2me | Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_restrict_atomSet_eq_sum_dirac
-- name    : BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:02:42.213529+00:00
-- url     : https://prove2.me/theorems/027e075a-30b8-4727-9685-9e42a3a34881
-- title:
--   `BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac` [IsFiniteMeasure mu] : mu.restrict (atomSet mu) = Measure.sum (fun x : atomSet mu => mu {(x : α)} • Measure.di
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasureAtomicDiffuse`.
--
--   `BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac` [IsFiniteMeasure mu] : mu.restrict (atomSet mu) = Measure.sum (fun x : atomSet mu => mu {(x : α)} • Measure.dirac (x : α))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac`.

-- Generated from ChapterMeasureAtomicDiffuse.lean — theorem BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse


noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

theorem BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac [IsFiniteMeasure mu] :
    mu.restrict (atomSet mu)
      = Measure.sum (fun x : atomSet mu => mu {(x : α)} • Measure.dirac (x : α)) := by sorry
