-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
-- name    : AvramDividend.Classical.avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T20:36:30.228045+00:00
-- url     : https://prove2.me/theorems/2453a94b-b50f-48a8-ac7d-b69b8070e400
-- title:
--   Zero-reserve BV exact discounted cash and stopped negative-jump compensator ceiling on one physical no-jump cell
-- statement:
--   Original BV finite-activity zero-reserve no-negative-jump cell. The closed-origin HJB ceiling c ≤ (q+λ)w(0), together with the proved exact weighted no-jump Stieltjes cash identity, gives a sharp discounted bound: cash plus the decrease in surviving discounted w(0) is at most λ w(0)exp(-qs)(t-s). This is exactly the compensator contribution of the zero-contact negative-jump count with coefficient -exp(-qs)w(0), with no O(Δ) discount error. The output is an arithmetic source obligation used in the true uniform-grid physical stopped excess estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
    (q rate w0 cash s t : ℝ)
    (hq : 0 < q) (hrate : 0 ≤ rate) (hw0 : 0 ≤ w0)
    (hst : s ≤ t)
    (hCash : cash ≤ (q + rate) * w0 *
      ((Real.exp (-(q * s)) - Real.exp (-(q * t))) / q)) :
    cash + Real.exp (-(q * t)) * w0 -
      Real.exp (-(q * s)) * w0 ≤
      rate * w0 * Real.exp (-(q * s)) * (t - s) := by sorry
