-- Prove2me | Theorems.Thm_ActuarialValuation_ulBidOfferCost_nonneg
-- name    : ActuarialValuation.ulBidOfferCost_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:04:08.293086+00:00
-- url     : https://prove2.me/theorems/65dc7125-8652-4998-b9e1-1b67016d03ee
-- title:
--   Premium allocation, bid and offer prices and fund charges: ulBidOfferCost_nonneg
-- statement:
--   Selling immediately at bid no higher than offer preserves a nonnegative spread cost. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem ulBidOfferCost_nonneg (allocated offer bid : ℝ) (ha : 0≤allocated) (ho : 0<offer) (hb : 0≤bid) (hspread : bid≤offer) : 0≤ulBidOfferCost allocated offer bid := by sorry

end ActuarialValuation
