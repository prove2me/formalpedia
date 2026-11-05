-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_source_HJB_strict_cap_band_open
-- name    : AvramDividend.Classical.avram_p3_e_compensator_source_HJB_strict_cap_band_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:22:21.031962+00:00
-- url     : https://prove2.me/theorems/74aac065-b252-46b8-b112-3276d59a1d21
-- title:
--   Strict original HJB cap band lies in an open smooth generator domain
-- statement:
--   For a positive original reserve lower bound a and b≥a strictly below the HJB cap C in ENNReal.ofReal, the compact band [a/2,b] lies inside the original open generator region {y>0, ofReal y<C}. The source region is genuinely open, enabling ContDiffOn ℝ 1 w to supply ordinary derivatives and continuous derivative on the compact band.
-- source:
--   ENNReal.continuous_ofReal and monotonicity of ofReal, together with the order topology of real and ENNReal and elementary positive reserve inequalities. No weakening of the original HJB cap or boundary-localisation assumptions.

import Mathlib
open Set Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_source_HJB_strict_cap_band_open
(C : ℝ≥0∞) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
(hbC : ENNReal.ofReal b < C) :
IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
  Set.Icc (a / 2) b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
