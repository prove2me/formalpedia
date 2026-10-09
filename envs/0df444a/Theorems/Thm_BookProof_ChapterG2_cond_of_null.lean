-- Prove2me | Theorems.Thm_BookProof_ChapterG2_cond_of_null
-- name    : BookProof.ChapterG2.cond_of_null
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:49:23.869206+00:00
-- url     : https://prove2.me/theorems/8bb165fe-3408-45c2-924e-f5eddf82c9ee
-- title:
--   `BookProof.ChapterG2.cond_of_null` (μ : Measure Ω) {C : Set Ω} (hC : μ C = 0) : μ[|C] = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.cond_of_null` (μ : Measure Ω) {C : Set Ω} (hC : μ C = 0) : μ[|C] = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.cond_of_null`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.cond_of_null
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2


open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.ChapterG2.cond_of_null (μ : Measure Ω) {C : Set Ω} (hC : μ C = 0) : μ[|C] = 0 := by sorry
