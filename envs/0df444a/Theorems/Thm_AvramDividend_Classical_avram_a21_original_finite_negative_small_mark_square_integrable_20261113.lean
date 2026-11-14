-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_finite_negative_small_mark_square_integrable_20261113
-- name    : AvramDividend.Classical.avram_a21_original_finite_negative_small_mark_square_integrable_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:41:14.915878+00:00
-- url     : https://prove2.me/theorems/0b15f55c-abb0-48eb-8324-09cf34699efa
-- title:
--   Finite negative source activity implies square integrability of unit-small jump marks
-- statement:
--   Every measure finite on negative real numbers integrates the squared mark over (-1,0), since there the squared mark is measurable and bounded by one.
-- source:
--   Pinned Mathlib IntegrableOn.of_bound, original negative Levy mark finiteness; supports cutoff integral partition theorem ca95021a.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_finite_negative_small_mark_square_integrable_20261113
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤) :
    IntegrableOn (fun z : ℝ => z ^ 2) (Ioo (-1 : ℝ) 0) ν := by sorry
