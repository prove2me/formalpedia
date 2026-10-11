-- Prove2me | Theorems.Thm_ActuarialValuation_ulSurrenderValue_le_fund
-- name    : ActuarialValuation.ulSurrenderValue_le_fund
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:08:02.232832+00:00
-- url     : https://prove2.me/theorems/e447e58c-8cf1-4c17-8f85-725bd3525c6a
-- title:
--   Risk guarantees, surrender payments and reserve strain: ulSurrenderValue_le_fund
-- statement:
--   A nonnegative surrender charge cannot increase the positive fund value. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulSurrenderValue

namespace ActuarialValuation

theorem ulSurrenderValue_le_fund (fund charge : ℝ) (hf : 0≤fund) (hc : 0≤charge) : ulSurrenderValue fund charge≤fund := by sorry

end ActuarialValuation
