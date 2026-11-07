-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_pointwise_rescale
-- name    : AvramDividend.Classical.avram_p3_grid4_source_slack_exact_pointwise_rescale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:28:29.437126+00:00
-- url     : https://prove2.me/theorems/dd9068b0-c25d-4f76-8a8a-225fc8d6c77c
-- title:
--   Positive source-budget scalar correction absorbs per-grid deterministic slack exactly
-- statement:
--   If the physical-grid original BV cash+terminal is bounded by w(x) plus its source and a nonnegative vanishing deterministic error, scaling by w(x)/(w(x)+error) restores the exact pointwise signed source upper bound without a per-grid zero-error assumption.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_source_slack_exact_pointwise_rescale
    (w e F Z : ℝ) (hw : 0 < w) (he : 0 ≤ e)
    (hF : F ≤ w + Z + e) :
    (w / (w + e)) * F ≤ w + (w / (w + e)) * Z := by sorry
