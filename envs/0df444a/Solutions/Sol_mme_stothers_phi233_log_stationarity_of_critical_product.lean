-- Prove2me | solution 1 for mme_stothers_phi233_log_stationarity_of_critical_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:41:45.4971+00:00
-- url     : https://prove2.me/submissions/6201a1ef-ffad-4681-b1ef-c49a170ba52a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-- The multiplicative critical-point equation for the `phi_233` profile is
equivalent to the logarithmic stationarity certificate used by the entropy
tangent bound. -/
theorem solution
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d)
    (hcritical : a ^ (2 : ℕ) * d = b ^ (2 : ℕ) * c) :
    2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0 := by
  have hlog := congrArg Real.log hcritical
  rw [Real.log_mul (pow_ne_zero 2 ha.ne') hd.ne',
    Real.log_mul (pow_ne_zero 2 hb.ne') hc.ne',
    Real.log_pow, Real.log_pow] at hlog
  rw [Real.log_div ha.ne' (by norm_num),
    Real.log_div hb.ne' (by norm_num),
    Real.log_div hc.ne' (by norm_num),
    Real.log_div hd.ne' (by norm_num)]
  norm_num at hlog ⊢
  linarith
