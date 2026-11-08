-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_nonpositive_finset_term_abs_le_sum_abs
-- name    : AvramDividend.Classical.avram_bv_residual9_nonpositive_finset_term_abs_le_sum_abs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:36:02.655935+00:00
-- url     : https://prove2.me/theorems/7b4b13df-da26-477d-b126-83d7e3b33a2a
-- title:
--   Any nonpositive finite generator sum bounds each cell's absolute value
-- statement:
--   A sharp finite-sum necessary-condition inequality: every nonpositive cell magnitude is bounded by the absolute sum, so integrability of the negative generator sum would force each cell L1. Does not assume or prove source random-generator integrability.
-- source:
--   BV-RESIDUAL9 original stopped HJB negative-cell algebra

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_nonpositive_finset_term_abs_le_sum_abs
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (hneg : ∀ i ∈ s, f i ≤ 0) :
    ∀ i ∈ s, |f i| ≤ |∑ j ∈ s, f j| := by sorry
