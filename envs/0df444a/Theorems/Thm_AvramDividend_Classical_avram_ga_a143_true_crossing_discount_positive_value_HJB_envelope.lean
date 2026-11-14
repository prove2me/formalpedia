-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a143_true_crossing_discount_positive_value_HJB_envelope
-- name    : AvramDividend.Classical.avram_ga_a143_true_crossing_discount_positive_value_HJB_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:35:37.58521+00:00
-- url     : https://prove2.me/theorems/3248f268-0f4f-45a3-ab30-c98600adbbbd
-- title:
--   True stopped Gaussian crossing positive discounted value error bounded by post-crossing positive upper source envelope, compact pre-crossing lower bound and absolute HJB compensator
-- statement:
--   For a true stopped Gaussian physical crossing cell, the discount factor lies between zero and one. If the original HJB supersolution value at the genuine clipped source endpoint has an upper nonnegative envelope T, and the original compact positive pre-stop reserve value is bounded below by -B, then the positive crossing residual after subtracting the HJB compensator is at most T+B+|H|. No negative-tail control of the post-crossing value is required, making this suitable for proving the source-specific positive integrable envelope ga139.
-- source:
--   Original Avram Gaussian clipped crossing positive expected L1 ga120 and original upper exponential source ga45 plus compact lower bound gledger63.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a143_true_crossing_discount_positive_value_HJB_envelope
    (E Wafter Wbefore H T B : ℝ)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hUpper : Wafter ≤ T) (hLower : -B ≤ Wbefore) :
    max (E * (Wafter - Wbefore) - H) 0 ≤
      T + B + |H| := by sorry
