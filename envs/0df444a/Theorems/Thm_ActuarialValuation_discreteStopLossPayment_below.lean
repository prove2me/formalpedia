-- Prove2me | Theorems.Thm_ActuarialValuation_discreteStopLossPayment_below
-- name    : ActuarialValuation.discreteStopLossPayment_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:26:59.091453+00:00
-- url     : https://prove2.me/theorems/9d627c2d-990b-4ab0-af37-03402977b77e
-- title:
--   Claims no larger than attachment have zero reinsurance payment
-- statement:
--   If the realised aggregate loss does not exceed the contractual attachment, no part of the claim reaches the reinsurer. Natural subtraction saturates at zero and exactly implements the stop-loss contract's payout rule.
--
--   **Mathematical statement**
--
--   $$
--   s\le d\Longrightarrow(s-d)_+=0
--   $$
-- source:
--   H H Panjer (1980), The aggregate claims distribution and stop-loss reinsurance, Transactions of the Society of Actuaries 32, 523–535; H H Panjer and G E Willmot (1982), Recursions for compound distributions, ASTIN Bulletin; Willmot, Drekic and Cai (2005), Equilibrium compound distributions and stop-loss moments, https://doi.org/10.1080/03461230510009691; exact finite discrete stop-loss specialisation

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPayment

namespace ActuarialValuation

theorem discreteStopLossPayment_below (claim deductible : ℕ)
  (h : claim ≤ deductible) :
  discreteStopLossPayment claim deductible = 0 := by sorry

end ActuarialValuation
