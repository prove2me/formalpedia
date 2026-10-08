-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLIntegral_exp_neg_mul_Ioi
-- name    : AvramDividend.Classical.positiveLIntegral_exp_neg_mul_Ioi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:45:00.239392+00:00
-- url     : https://prove2.me/theorems/dc86a30a-9ecc-4348-9bdc-6f1f0d721792
-- title:
--   Positive lintegral of a decaying exponential tail
-- statement:
--   For s>0 and any real z, the nonnegative Lebesgue integral of exp(-s x) over x>z equals exp(-s z)/s. This is the ENNReal form of the standard improper exponential integral.
-- source:
--   Pinned Mathlib Analysis.SpecialFunctions.ImproperIntegrals theorems integrableOn_exp_mul_Ioi and integral_exp_mul_Ioi, together with MeasureTheory.ofReal_integral_eq_lintegral_ofReal. This is the inner integral required by the Tonelli proof of the renewal cumulative Laplace identity.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- The nonnegative Lebesgue integral of exp(-s x) over (z,∞) is
exp(-s z)/s when s>0. -/
theorem positiveLIntegral_exp_neg_mul_Ioi (s z : ℝ) (hs : 0 < s) :
    (∫⁻ x : ℝ in Ioi z, ENNReal.ofReal (Real.exp (-s * x))) =
      ENNReal.ofReal (Real.exp (-s * z) / s) := by
  sorry

end AvramDividend.Classical
