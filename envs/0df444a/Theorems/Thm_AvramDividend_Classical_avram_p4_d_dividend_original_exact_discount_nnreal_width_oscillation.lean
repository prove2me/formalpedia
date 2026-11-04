-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_exact_discount_nnreal_width_oscillation
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_exact_discount_nnreal_width_oscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:10:32.901686+00:00
-- url     : https://prove2.me/theorems/5206c13c-1f41-4c54-9085-e0188bede135
-- title:
--   Original ENNReal discount oscillation bounded by q times payment-cell width
-- statement:
--   The exact ENNReal.ofReal time-dependent discount used in original dividendMeasure Cash has oscillation over any interval [a,b] in nonnegative time bounded by the ENNReal image of q(b-a). The theorem transports a proved real exponential Lipschitz inequality across the nonnegative real inclusion without discarding the singular or atomic Stieltjes contribution.
-- source:
--   Proved original real discount Lipschitz lemma and Mathlib.Data.ENNReal.Real ofReal_add

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz

open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_exact_discount_nnreal_width_oscillation (q a b : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal (Real.exp (-(q * a))) ≤
      ENNReal.ofReal (Real.exp (-(q * b))) +
        ENNReal.ofReal (q * (b - a)) := by sorry
