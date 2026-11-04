-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_finite_ennreal_moment_normalised_ofReal
-- name    : AvramDividend.Classical.avram_p2_b_rate_finite_ennreal_moment_normalised_ofReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:13:17.20198+00:00
-- url     : https://prove2.me/theorems/62e1f24c-8228-4faa-932a-45a879a8a5c2
-- title:
--   Finite extended-real moment converts to the normalised time-divided moment
-- statement:
--   For every finite nonnegative extended real moment and positive real time h, the extended-real lifting of the corresponding real moment divided by h is exactly division in ENNReal by ofReal h. This bridges original real-valued small-time rate limits to weighted-image measure moment normalisation.

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Basic

open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_finite_ennreal_moment_normalised_ofReal (a : ℝ≥0∞) (ha : a ≠ ⊤) (h : ℝ) (hh : 0 < h) :
  ENNReal.ofReal (a.toReal / h) = a / ENNReal.ofReal h := by sorry
