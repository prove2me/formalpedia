-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_matrixModel_B_ne_zero
-- name    : BookProof.GaugeFixing.matrixModel_B_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:27:17.653936+00:00
-- url     : https://prove2.me/theorems/c71c608b-60e2-4bcc-b469-875c5b80bec3
-- title:
--   In the model the Nakanishi–Lautrup field is non-zero
-- statement:
--   In the model the Nakanishi–Lautrup field is non-zero.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.matrixModel_B_ne_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 347–349.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L347-L349

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.matrixModel_B_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.matrixModel_B_ne_zero : (matrixModel.B : Mat2) ≠ 0 := by sorry
