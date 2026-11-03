-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_positive_cap_iff_nonempty_real_hjb_interior
-- name    : AvramDividend.Classical.avram_wave7_09_positive_cap_iff_nonempty_real_hjb_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:39:06.659197+00:00
-- url     : https://prove2.me/theorems/a90cee40-832c-42cc-b806-dd62cdc2b904
-- title:
--   Exact non-vacuity criterion for the canonical ENNReal-capped HJB verification interior
-- statement:
--   For every original extended-nonnegative dividend reserve cap C, the canonical real HJB interior {y:0<y and ENNReal.ofReal y<C} has an actual real point if and only if C>0. The forward implication is immediate by positivity of ENNReal.ofReal. For C=∞, the point y=1 works. For a finite positive C, its positive real half-cap y=C.toReal/2 lies strictly inside by the exact ENNReal.ofReal/toReal order comparison. This formally certifies that zero-cap HJB assumptions are vacuous, while every strictly positive cap, including infinite cap, supplies a nontrivial region. It complements the Proved openness theorem bcf24f3a and the corrected positive-cap parent 8c16239e.
-- source:
--   Pinned Mathlib ENNReal.toReal_pos, ENNReal.ofReal_toReal and ENNReal.ofReal_lt_ofReal_iff; exact canonical cap geometry and Proved prior open-domain theorem bcf24f3a. No Open imports or altered stochastic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_positive_cap_iff_nonempty_real_hjb_interior
    (C : ℝ≥0∞) :
    (∃ y : ℝ, 0 < y ∧ ENNReal.ofReal y < C) ↔ 0 < C := by sorry
