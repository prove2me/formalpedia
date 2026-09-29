-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_addDeg_snd
-- name    : BookProof.GaugeFixing.addDeg_snd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:25:30.834734+00:00
-- url     : https://prove2.me/theorems/496d7c45-ae4c-478c-8ff3-8c9ce510b376
-- title:
--   Second component of the bidegree addition
-- statement:
--   Second component of the bidegree addition.
--
--   For bidegrees $a,b$ the degree addition satisfies
--   $$
--   \text{addDeg}(a,b)_2 = a_2 + b_2.
--   $$
--
--   This is the second projection of the componentwise addition on the bidegree monoid used to grade the gauge-fixing BRST complex.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.addDeg_snd` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 88–88.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L88-L88

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.addDeg_snd
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing

theorem BookProof.GaugeFixing.addDeg_snd (a b : BiDegree) : (addDeg a b).2 = a.2 + b.2 := by sorry
