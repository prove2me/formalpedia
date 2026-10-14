-- Prove2me | Theorems.Thm_ActuarialValuation_ulDiscountedProfit_nonneg
-- name    : ActuarialValuation.ulDiscountedProfit_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:09:32.711599+00:00
-- url     : https://prove2.me/theorems/3fd6e12a-3281-43fb-82dd-0faf02c954d2
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulDiscountedProfit_nonneg
-- statement:
--   Nonnegative profits yield nonnegative present values under nonnegative discount factors. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \Pi=\sum_t v^t p_t\left(\text{income}_t-\text{outgo}_t\right)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 16. FCA, Unit-linked pensions and savings price and value practices, https://www.fca.org.uk/publications/multi-firm-reviews/unit-linked-pensions-and-savings-multi-firm-review-consumer-duty-price-and-value-practices; FCA TR16/2 Fair treatment of long-standing customers, https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02. Parent topic: Allocated premium, offer and bid unit prices, cost of allocation spread, fund charges, net amount at risk, policy expenses and discounted expected non-unit profit. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDiscountedProfit

namespace ActuarialValuation

theorem ulDiscountedProfit_nonneg (profit discount : ℝ) (hp : 0≤profit) (hd : 0≤discount) : 0≤ulDiscountedProfit profit discount := by sorry

end ActuarialValuation
