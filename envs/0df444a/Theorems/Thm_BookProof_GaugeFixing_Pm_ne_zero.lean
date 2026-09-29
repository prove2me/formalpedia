-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_Pm_ne_zero
-- name    : BookProof.GaugeFixing.Pm_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:23:31.887738+00:00
-- url     : https://prove2.me/theorems/5da251dc-3dd8-4285-bf51-64067c062137
-- title:
--   The gauge-fixing projection is nonzero
-- statement:
--   The gauge-fixing projection is nonzero.
--
--   In the $2\times2$ matrix model the projection $P_m$ is not the zero matrix.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.Pm_ne_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 274–277.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L274-L277

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.Pm_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.Pm_ne_zero : Pm ≠ 0 := by sorry
