-- Prove2me | Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_mem_atomSet_iff
-- name    : BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:01:19.663869+00:00
-- url     : https://prove2.me/theorems/82ef1b43-fa94-4842-9f0e-b5ae801f96ed
-- title:
--   `BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff` (x : α) : x ∈ atomSet mu ↔ mu {x} ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasureAtomicDiffuse`.
--
--   `BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff` (x : α) : x ∈ atomSet mu ↔ mu {x} ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff`.

-- Generated from ChapterMeasureAtomicDiffuse.lean — theorem BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse


noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

theorem BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff (x : α) : x ∈ atomSet mu ↔ mu {x} ≠ 0 := by sorry
