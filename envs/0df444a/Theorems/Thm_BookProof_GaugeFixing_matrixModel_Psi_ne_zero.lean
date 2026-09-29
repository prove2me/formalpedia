-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_matrixModel_Psi_ne_zero
-- name    : BookProof.GaugeFixing.matrixModel_Psi_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:07:16.982495+00:00
-- url     : https://prove2.me/theorems/ca92a893-c1bb-4300-9313-77564dc629fd
-- title:
--   In the model the Gauge-Fixing Fermion is non-zero
-- statement:
--   In the model the Gauge-Fixing Fermion is non-zero.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.matrixModel_Psi_ne_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 355–357.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L355-L357

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.matrixModel_Psi_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.matrixModel_Psi_ne_zero : (Psi matrixModel : Mat2) ≠ 0 := by sorry
