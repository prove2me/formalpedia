-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_min_eq_inter
-- name    : AvramDividend.Classical.paymentTimes_min_eq_inter
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:02:33.407113+00:00
-- url     : https://prove2.me/theorems/b3cc32fa-ff1c-49a0-8bff-ca3716e780bf
-- title:
--   Payment times for a minimum stopping clock are exactly the intersection of payment-time sets
-- statement:
--   For two arbitrary extended nonnegative stopping clocks σ and τ, the selected payment-time set under their minimum equals the intersection of their payment-time sets. The equality includes the initial time-zero dividend atom, even if either clock is zero. It gives a reusable set-theoretic decomposition for stopped Stieltjes reward integrals.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_min_eq_inter
    (σ τ : ℝ≥0∞) :
    paymentTimes (min σ τ) = paymentTimes σ ∩ paymentTimes τ := by sorry
