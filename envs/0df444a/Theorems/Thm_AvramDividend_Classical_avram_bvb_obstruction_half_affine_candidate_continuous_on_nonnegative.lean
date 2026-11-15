-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_candidate_continuous_on_nonnegative
-- name    : AvramDividend.Classical.avram_bvb_obstruction_half_affine_candidate_continuous_on_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T01:00:13.556317+00:00
-- url     : https://prove2.me/theorems/946421a7-12ce-47c1-bcd5-e88c1bbe70e6
-- title:
--   Half-unit affine zero-boundary verification candidate is continuous on nonnegative reserves
-- statement:
--   The piecewise affine BV verification candidate w(y)=0 for y<0 and 1/2+y for y≥0 is continuous on [0,∞), despite a permissible jump at the negative-to-nonnegative boundary. This supplies the exact candidate continuity hypothesis for the original positive-cap counterexample.
-- source:
--   On nonnegative reserves, the conditional expression equals the affine continuous map y↦1/2+y. Apply ContinuousOn.congr to this equality on Ici0.

import Mathlib
open Set Real

theorem AvramDividend.Classical.avram_bvb_obstruction_half_affine_candidate_continuous_on_nonnegative :
    ContinuousOn (fun u : ℝ => if u < 0 then 0 else 1 / 2 + u) (Ici 0) := by sorry
