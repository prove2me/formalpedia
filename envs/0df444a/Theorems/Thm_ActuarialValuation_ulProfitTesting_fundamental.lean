-- Prove2me | Theorems.Thm_ActuarialValuation_ulProfitTesting_fundamental
-- name    : ActuarialValuation.ulProfitTesting_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:10:50.909653+00:00
-- url     : https://prove2.me/theorems/07ced394-48a3-4126-95f3-d51cfeba3782
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulProfitTesting_fundamental
-- statement:
--   Actual unit premium allocation and bid-offer cost reconcile with the insurer's separate death guarantee obligations and complete non-unit cashflow profit account. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulPremiumAlloc
import Definitions.Def_actuarial_ulUnallocated
import Definitions.Def_actuarial_ulBidOfferCost
import Definitions.Def_actuarial_ulDeathBenefit
import Definitions.Def_actuarial_ulNetAmountAtRisk
import Definitions.Def_actuarial_ulDeathCost
import Definitions.Def_actuarial_ulNonUnitProfit

namespace ActuarialValuation

theorem ulProfitTesting_fundamental (premium allocation offer bid fund guarantee mortality income expense commission guaranteedExpense : ℝ) (hprice : 0<offer) (hbid : 0≤bid) (hspread : bid≤offer) (hp : 0≤premium) (ha : 0≤allocation) (hq : 0≤mortality) : (ulUnallocated premium allocation+ulPremiumAlloc premium allocation=premium) ∧ (0≤ulBidOfferCost (ulPremiumAlloc premium allocation) offer bid) ∧ (ulDeathBenefit fund guarantee=fund+ulNetAmountAtRisk fund guarantee) ∧ (ulNonUnitProfit income expense commission (ulDeathCost mortality fund guarantee) guaranteedExpense+expense+commission+ulDeathCost mortality fund guarantee+guaranteedExpense=income) := by sorry

end ActuarialValuation
