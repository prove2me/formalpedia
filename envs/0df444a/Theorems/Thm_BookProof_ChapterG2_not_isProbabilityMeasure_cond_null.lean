-- Prove2me | Theorems.Thm_BookProof_ChapterG2_not_isProbabilityMeasure_cond_null
-- name    : BookProof.ChapterG2.not_isProbabilityMeasure_cond_null
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:49:32.00819+00:00
-- url     : https://prove2.me/theorems/d214ca8d-53f0-4a1f-90da-8cee0dd06bcb
-- title:
--   `BookProof.ChapterG2.not_isProbabilityMeasure_cond_null` (μ : Measure Ω) {C : Set Ω} (hC : μ C = 0) : ¬ IsProbabilityMeasure μ[|C]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.not_isProbabilityMeasure_cond_null` (μ : Measure Ω) {C : Set Ω} (hC : μ C = 0) : ¬ IsProbabilityMeasure μ[|C]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.not_isProbabilityMeasure_cond_null`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.not_isProbabilityMeasure_cond_null
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2


open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.ChapterG2.not_isProbabilityMeasure_cond_null (μ : Measure Ω) {C : Set Ω}
    (hC : μ C = 0) : ¬ IsProbabilityMeasure μ[|C] := by sorry
