-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a50_small_drift_large_raw_increment_energy_le_centered
-- name    : AvramDividend.Classical.avram_ga_a50_small_drift_large_raw_increment_energy_le_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:10:48.386198+00:00
-- url     : https://prove2.me/theorems/3924565b-dfde-4d0d-ae10-04096310027a
-- title:
--   Small deterministic drift makes raw Gaussian large-increment quadratic energy dominated by centred large-cell energy
-- statement:
--   When the drift shift is at most half a positive excursion threshold, the raw Gaussian source squared-increment energy above the threshold is at most four times the centred squared-increment energy above half the threshold.
-- source:
--   Direct conversion needed in original stopped Gaussian b0d9951c from proved centred Lindeberg to raw spatial Taylor C2 increment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a50_small_drift_large_raw_increment_energy_le_centered (z d η : ℝ) (hη : 0 < η)
    (hDrift : |d| ≤ η / 2) :
    (if η ≤ |z + d| then (z + d) ^ 2 else 0) ≤
      4 * (if η / 2 ≤ |z| then z ^ 2 else 0) := by sorry
