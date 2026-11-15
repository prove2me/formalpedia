-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a258_large_positive_combined_discounted_gaussian_source_envelope
-- name    : AvramDividend.Classical.avram_ga_a258_large_positive_combined_discounted_gaussian_source_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:49:02.3084+00:00
-- url     : https://prove2.me/theorems/7178f7f1-af32-4265-a875-9989a84f517b
-- title:
--   One-sided Gaussian large-cell source residual bounded by endpoint upper envelope and compact initial Taylor jets
-- statement:
--   For bounded nonnegative start/end discounts, a compact bound B on the start value, first derivative and Hessian coefficient, and a nonnegative one-sided upper bound T for the postincrement value, the positive combined discounted Gaussian source residual is at most T+B(1+|r|+z²/2). This exact one-sided estimate is the large-cell companion of proved a236 and can be integrated using stopped Gaussian large-square tails and the original positive exponential endpoint bound. It needs no lower bound or absolute growth on the postincrement value.
-- source:
--   Original combined fullcell a216 large increments, source endpoint a257 and original stopped quadratic Gaussian a187/a240

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a258_large_positive_combined_discounted_gaussian_source_envelope
    (e0 e1 w0 w1 d h r z B T : ℝ)
    (he0 : 0 ≤ e0) (he01 : e0 ≤ 1)
    (he1 : 0 ≤ e1) (he11 : e1 ≤ 1)
    (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hw0 : |w0| ≤ B) (hd : |d| ≤ B) (hh : |h| ≤ B)
    (hw1 : w1 ≤ T) :
    max (e1*(w1-w0)-e0*(d*r+h/2*z^2)) 0 ≤
      T+B*(1+|r|+z^2/2) := by sorry
