-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_hjb_drift_two_scalar
-- name    : AvramDividend.Classical.avram_a19_affine_singular_hjb_drift_two_scalar
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:43:00.634821+00:00
-- url     : https://prove2.me/theorems/ba643794-048b-4187-9545-c72de73e3510
-- title:
--   Singular affine HJB deficit is nonpositive with physical drift two
-- statement:
--   The explicit singular affine reserve HJB expression with physical drift two is nonpositive for every reserve strictly above zero and at most one.
-- source:
--   A19 original-generator countermodel, singular Levy density on (-1,0), affine zero-extension; real arithmetic sign check.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_a19_affine_singular_hjb_drift_two_scalar
    (x : ℝ) (hx : 0 < x) (hcap : x ≤ 1) :
    5 + x - 4 * Real.sqrt x - 2 / Real.sqrt x ≤ 0 := by sorry
