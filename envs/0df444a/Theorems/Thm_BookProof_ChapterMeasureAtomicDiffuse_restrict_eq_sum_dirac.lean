-- Prove2me | Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_restrict_eq_sum_dirac
-- name    : BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:02:23.140445+00:00
-- url     : https://prove2.me/theorems/45c7e1ab-a6b6-4b82-a873-2e72837b6118
-- title:
--   `BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac` {A : Set α} (hc : A.Countable) : mu.restrict A = Measure.sum (fun x : A => mu {(x : α)} • Measure.dirac (x : α))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasureAtomicDiffuse`.
--
--   `BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac` {A : Set α} (hc : A.Countable) : mu.restrict A = Measure.sum (fun x : A => mu {(x : α)} • Measure.dirac (x : α))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac`.

-- Generated from ChapterMeasureAtomicDiffuse.lean — theorem BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse


noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

theorem BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac {A : Set α} (hc : A.Countable) :
    mu.restrict A = Measure.sum (fun x : A => mu {(x : α)} • Measure.dirac (x : α)) := by sorry
