-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_real_negative_cutoff_strip_subset_unit_20261113
-- name    : AvramDividend.Classical.avram_a21_real_negative_cutoff_strip_subset_unit_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:24:10.266202+00:00
-- url     : https://prove2.me/theorems/8f7b7e03-6983-4c4c-a0bd-18470ad02ccb
-- title:
--   Negative source cutoff strips lie within the unit-negative interval
-- statement:
--   Every negative strip between cutoffs -1/(n+1) and -1/(m+1), with endpoints as in the source intrinsic Lévy mark definitions, lies within [-1,0].
-- source:
--   Elementary real order arithmetic. Supports negative Borel simple mark quantisation in original source certificate 67336b2d.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_a21_real_negative_cutoff_strip_subset_unit_20261113
    (n m : ℕ) :
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))) ⊆
      Icc (-1 : ℝ) 0 := by sorry
