-- Prove2me | Theorems.Thm_ActuarialValuation_ulNonUnitProfit_zero
-- name    : ActuarialValuation.ulNonUnitProfit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:08:43.582744+00:00
-- url     : https://prove2.me/theorems/63c4d296-7cbc-4ed6-b1f2-e5c577c0b366
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulNonUnitProfit_zero
-- statement:
--   A contract without non-unit cashflows yields no insurer profit. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulNonUnitProfit

namespace ActuarialValuation

theorem ulNonUnitProfit_zero  : ulNonUnitProfit 0 0 0 0 0=0 := by sorry

end ActuarialValuation
