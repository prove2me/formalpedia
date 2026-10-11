-- Prove2me | Theorems.Thm_ActuarialValuation_ulBidOfferCost_zero
-- name    : ActuarialValuation.ulBidOfferCost_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:03:55.562601+00:00
-- url     : https://prove2.me/theorems/e1fe4754-a63f-4eb3-9fae-cb670c2cc6d9
-- title:
--   Premium allocation, bid and offer prices and fund charges: ulBidOfferCost_zero
-- statement:
--   No bid-offer spread produces no immediate allocation value loss. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U_t=U_{t-1}+\frac{a_t P_t}{O_t}-\frac{C_t}{B_t}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 16. FCA, Unit-linked pensions and savings price and value practices, https://www.fca.org.uk/publications/multi-firm-reviews/unit-linked-pensions-and-savings-multi-firm-review-consumer-duty-price-and-value-practices; FCA TR16/2 Fair treatment of long-standing customers, https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02. Parent topic: Allocated premium, offer and bid unit prices, cost of allocation spread, fund charges, net amount at risk, policy expenses and discounted expected non-unit profit. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulBidOfferCost

namespace ActuarialValuation

theorem ulBidOfferCost_zero (allocated price : ℝ) (h : price≠0) : ulBidOfferCost allocated price price=0 := by sorry

end ActuarialValuation
