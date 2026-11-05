-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f2_bonferroni_void_rate_squeeze_atTop
-- name    : AvramDividend.Classical.avram_p4_f2_bonferroni_void_rate_squeeze_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:00:07.609028+00:00
-- url     : https://prove2.me/theorems/6d362474-4717-43c2-b2a8-f1247b0bf970
-- title:
--   Second-order Bonferroni inequalities imply the exact small-time void rate
-- statement:
--   If for all positive integers k the scaled occurrence probabilities k p(k) lie between r − (r²/2)/k and r, then k p(k) tends to r as k tends to infinity. This is the exact deterministic squeeze needed to convert source finite-band first and factorial moment estimates into a small-time void intensity slope.
-- source:
--   The source-specific original nonvoid moment inequality avram_p4_f2_original_negative_band_nonvoid_second_order_bound and original target 17372d7a reduce to these bounds after exact k-scaled source-rate conversion.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f2_bonferroni_void_rate_squeeze_atTop
    (r : ℝ) (p : ℕ → ℝ)
    (hBound : ∀ k : ℕ, 0 < k →
      r - (r ^ 2 / 2) * (k : ℝ)⁻¹ ≤ (k : ℝ) * p k ∧
      (k : ℝ) * p k ≤ r) :
    Filter.Tendsto (fun k : ℕ => (k : ℝ) * p k)
      Filter.atTop (nhds r) := by sorry
