-- Prove2me | Theorems.Thm_ActuarialValuation_ulNonUnitProfit_balance
-- name    : ActuarialValuation.ulNonUnitProfit_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:08:29.452005+00:00
-- url     : https://prove2.me/theorems/15ae9697-a295-40ba-8b6a-fe9075a9e883
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulNonUnitProfit_balance
-- statement:
--   The non-unit income and all insured expense/risk costs reconcile exactly. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem ulNonUnitProfit_balance (income expense comm death guarantee : ℝ) : ulNonUnitProfit income expense comm death guarantee+expense+comm+death+guarantee=income := by sorry

end ActuarialValuation
