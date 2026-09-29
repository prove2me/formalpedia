-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_Qm_ne_zero
-- name    : BookProof.GaugeFixing.Qm_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:24:14.069603+00:00
-- url     : https://prove2.me/theorems/ebae4a5f-a1c4-46a1-91b2-51219b9f83c2
-- title:
--   The BRST charge matrix is nonzero
-- statement:
--   The BRST charge matrix is nonzero.
--
--   In the $2\times2$ matrix model the BRST charge matrix $Q_m$ is not the zero matrix, so the model's BRST differential is non-trivial.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.Qm_ne_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 269–272.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L269-L272

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.Qm_ne_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.Qm_ne_zero : Qm ≠ 0 := by sorry
