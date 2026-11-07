-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_strict_negative_cutoff_mark_weight_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_strict_negative_cutoff_mark_weight_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:18:40.21346+00:00
-- url     : https://prove2.me/theorems/1ba826da-d5a1-40a7-8978-0a5c74497247
-- title:
--   Borel measurability of exact intrinsic strictly negative marked jump-magnitude cutoff weight
-- statement:
--   The original intrinsic marked jump-size cutoff weight z↦(-z)₊1{z<-1/(k+1)} is an extended nonnegative Borel function; its strict threshold and sign are unchanged.
-- source:
--   Measurable.ite on the open cutoff half-line, composed ENNReal.ofReal with real negation. Required in the exact weighted shift / frozen-prefix lintegral transport, no Poisson premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_strict_negative_cutoff_mark_weight_measurable
    (k : ℕ) :
    Measurable (fun z : ℝ => if z < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-z) else 0) := by sorry
