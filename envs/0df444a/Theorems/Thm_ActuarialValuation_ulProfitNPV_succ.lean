-- Prove2me | Theorems.Thm_ActuarialValuation_ulProfitNPV_succ
-- name    : ActuarialValuation.ulProfitNPV_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:09:59.948105+00:00
-- url     : https://prove2.me/theorems/bf42f1e5-f6c8-4317-9912-9ed8bf534b72
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulProfitNPV_succ
-- statement:
--   Each policy year contributes one discounted insurer profit. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulProfitNPV

namespace ActuarialValuation

theorem ulProfitNPV_succ (cash discount : ℕ → ℝ) (n : ℕ) : ulProfitNPV cash discount (n+1)=ulProfitNPV cash discount n+ulDiscountedProfit (cash n) (discount n) := by sorry

end ActuarialValuation
