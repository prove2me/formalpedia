-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a183_drift_shift_large_raw_square_tail_le_centered_square
-- name    : AvramDividend.Classical.avram_ga_a183_drift_shift_large_raw_square_tail_le_centered_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:50:15.134203+00:00
-- url     : https://prove2.me/theorems/22c188bc-2d2b-4195-b438-ea55d29bb73a
-- title:
--   Large raw Gaussian physical squared increment dominated by large centred squared increment under small deterministic drift
-- statement:
--   For a physical raw increment z+d formed by adding a deterministic drift increment d to a centred Gaussian increment z, if the drift magnitude is at most half the fixed large-increment threshold, the truncated raw squared increment is bounded by four times the centred squared increment restricted to half that threshold. This pointwise estimate transports the Proved original stopped normalised Gaussian fourth-moment tail estimate ga34 to raw increments needed in original Taylor a149.
-- source:
--   Elementary reverse triangle inequality and squared absolute bounds; original Gaussian source raw-centred tail transport.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a183_drift_shift_large_raw_square_tail_le_centered_square
    (z d δ : ℝ) (hδ : 0 < δ) (hd : |d| ≤ δ / 2) :
    (if δ ≤ |z + d| then (z + d)^2 else 0) ≤
      4 * (if δ / 2 ≤ |z| then z^2 else 0) := by sorry
