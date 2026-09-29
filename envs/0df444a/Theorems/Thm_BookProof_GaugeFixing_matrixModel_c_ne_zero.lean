-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_matrixModel_c_ne_zero
-- name    : BookProof.GaugeFixing.matrixModel_c_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:56:44.996718+00:00
-- url     : https://prove2.me/theorems/c3b5af3c-3668-438a-8cd7-8f00cef216fb
-- title:
--   In the model the ghost is non-zero, so `s_c_eq_zero` is not vacuous
-- statement:
--   In the model the ghost is non-zero, so `s_c_eq_zero` is not vacuous.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.matrixModel_c_ne_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 343–345.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L343-L345

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.matrixModel_c_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.matrixModel_c_ne_zero : (matrixModel.c : Mat2) ≠ 0 := by sorry
