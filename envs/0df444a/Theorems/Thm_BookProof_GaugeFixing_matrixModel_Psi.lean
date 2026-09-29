-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_matrixModel_Psi
-- name    : BookProof.GaugeFixing.matrixModel_Psi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:56:06.482291+00:00
-- url     : https://prove2.me/theorems/8789b156-8960-48cd-86b5-e0d9d254587c
-- title:
--   In the model the Gauge-Fixing Fermion is the anti-ghost itself
-- statement:
--   In the model the Gauge-Fixing Fermion is the anti-ghost itself.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.matrixModel_Psi` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 351–353.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L351-L353

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.matrixModel_Psi
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.matrixModel_Psi : (Psi matrixModel : Mat2) = Pm := by sorry
