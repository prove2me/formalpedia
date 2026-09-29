-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_s_gaugeField
-- name    : BookProof.GaugeFixing.s_gaugeField
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:57:28.947946+00:00
-- url     : https://prove2.me/theorems/08a55052-0790-4437-a9ae-b933565cf6c7
-- title:
--   The BRST variation of `v − dφ` is the ghost: `s (v − dφ) = c`
-- statement:
--   The BRST variation of `v − dφ` is the ghost: `s (v − dφ) = c`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.s_gaugeField` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 178–182.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L178-L182

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.s_gaugeField
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.s_gaugeField : S.s (gaugeField S) = S.c := by sorry
