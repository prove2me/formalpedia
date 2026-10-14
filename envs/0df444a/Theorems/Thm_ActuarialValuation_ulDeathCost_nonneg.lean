-- Prove2me | Theorems.Thm_ActuarialValuation_ulDeathCost_nonneg
-- name    : ActuarialValuation.ulDeathCost_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:06:58.137698+00:00
-- url     : https://prove2.me/theorems/d76998b0-c274-42b0-8037-7078bcc68b61
-- title:
--   Risk guarantees, surrender payments and reserve strain: ulDeathCost_nonneg
-- statement:
--   Expected non-unit death cost is nonnegative at a valid mortality rate. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   B_t^{\text{death}}=\max(F_t,G_t),\quad R_t=(G_t-F_t)^+
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 16. FCA, Unit-linked pensions and savings price and value practices, https://www.fca.org.uk/publications/multi-firm-reviews/unit-linked-pensions-and-savings-multi-firm-review-consumer-duty-price-and-value-practices; FCA TR16/2 Fair treatment of long-standing customers, https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02. Parent topic: Allocated premium, offer and bid unit prices, cost of allocation spread, fund charges, net amount at risk, policy expenses and discounted expected non-unit profit. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathCost

namespace ActuarialValuation

theorem ulDeathCost_nonneg (q fund guarantee : ℝ) (hq : 0≤q) : 0≤ulDeathCost q fund guarantee := by sorry

end ActuarialValuation
