-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a270_negative_large_Gaussian_raw_exponential_absorbed_by_quadratic_tail
-- name    : AvramDividend.Classical.avram_ga_a270_negative_large_Gaussian_raw_exponential_absorbed_by_quadratic_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:04:28.131201+00:00
-- url     : https://prove2.me/theorems/844183a2-02fa-4a69-958c-c3628ee7672d
-- title:
--   Gaussian two-sided rare raw event exponential controlled by positive Gaussian exponential tail or raw quadratic tail
-- statement:
--   On a rare Gaussian raw increment event |r|≥δ, an exponential exp(theta r) with nonnegative theta is bounded by itself on positive rare events r≥δ, and otherwise by r²/δ² on negative rare events. Thus the full signed two-tail exponential endpoint source reduces to proven original positive exponential expected L1 a233 and proven original raw large-square expected L1 a187, without imposing a two-sided exponential moment on the postpayment value.
-- source:
--   Original source a216 large-event exponential endpoint upper + a233 positive raw exp and a187 raw large-square tails

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a270_negative_large_Gaussian_raw_exponential_absorbed_by_quadratic_tail
    (theta delta r : ℝ) (hθ : 0 ≤ theta) (hδ : 0 < delta)
    (hLarge : delta ≤ |r|) :
    Real.exp (theta*r) ≤
      (if delta ≤ r then Real.exp (theta*r) else r^2/delta^2) := by sorry
