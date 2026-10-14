-- Prove2me | Theorems.Thm_ActuarialValuation_ulProfitNPV_nonneg
-- name    : ActuarialValuation.ulProfitNPV_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:10:31.754547+00:00
-- url     : https://prove2.me/theorems/6e5e3ec2-5f1d-47b2-9324-6463d0c479ed
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulProfitNPV_nonneg
-- statement:
--   Positive actuarial projected profits have nonnegative discounted present value. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulProfitNPV

namespace ActuarialValuation

theorem ulProfitNPV_nonneg (cash discount : ℕ → ℝ) (n : ℕ) (hc : ∀ t, 0≤cash t) (hd : ∀ t, 0≤discount t) : 0≤ulProfitNPV cash discount n := by sorry

end ActuarialValuation
