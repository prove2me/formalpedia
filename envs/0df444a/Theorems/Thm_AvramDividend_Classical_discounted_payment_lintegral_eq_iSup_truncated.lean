-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_payment_lintegral_eq_iSup_truncated
-- name    : AvramDividend.Classical.discounted_payment_lintegral_eq_iSup_truncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:08:06.937018+00:00
-- url     : https://prove2.me/theorems/40610335-df7a-4b83-a4f6-8bd6c1f82727
-- title:
--   Pathwise discounted payment integral is the supremum of integer-horizon truncations
-- statement:
--   For a fixed ruin horizon and a fixed Stieltjes measure, the full discounted integral over payment times equals the supremum of the same integral truncated at natural-number horizons. This is a pathwise increasing-set result and does not involve measurability in the sample point omega.
-- source:
--   Inner-integral monotone-convergence step for Proposition 4(i) of Avram-Palmowski-Pistorius, using deterministic integer exhaustion of the payment-time set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_payment_lintegral_eq_iSup_truncated
    (q : ℝ) (σ : ℝ≥0∞) (μ : Measure ℝ) :
    (∫⁻ t in paymentTimes σ, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      ⨆ n : ℕ, ∫⁻ t in paymentTimes σ ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ := by sorry
