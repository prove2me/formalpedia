-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_addDeg_fst
-- name    : BookProof.GaugeFixing.addDeg_fst
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:24:44.287036+00:00
-- url     : https://prove2.me/theorems/aaed877e-c5af-4f61-84e2-617fb9b7fc29
-- title:
--   First component of the bidegree addition
-- statement:
--   First component of the bidegree addition.
--
--   For bidegrees $a,b$ the degree addition satisfies
--   $$
--   \text{addDeg}(a,b)_1 = a_1 + b_1.
--   $$
--
--   This is the first projection of the componentwise addition on the bidegree monoid used to grade the gauge-fixing BRST complex.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.addDeg_fst` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 86–86.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L86-L86

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.addDeg_fst
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing

theorem BookProof.GaugeFixing.addDeg_fst (a b : BiDegree) : (addDeg a b).1 = a.1 + b.1 := by sorry
