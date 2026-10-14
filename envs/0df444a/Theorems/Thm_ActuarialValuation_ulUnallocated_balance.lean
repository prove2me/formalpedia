-- Prove2me | Theorems.Thm_ActuarialValuation_ulUnallocated_balance
-- name    : ActuarialValuation.ulUnallocated_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:02:59.506471+00:00
-- url     : https://prove2.me/theorems/947b0313-d399-44da-a8c0-5017308a1a54
-- title:
--   Premium allocation, bid and offer prices and fund charges: ulUnallocated_balance
-- statement:
--   Every gross premium pound is either allocated to units or retained. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulPremiumAlloc
import Definitions.Def_actuarial_ulUnallocated

namespace ActuarialValuation

theorem ulUnallocated_balance (premium rate : ℝ) : ulUnallocated premium rate+ulPremiumAlloc premium rate=premium := by sorry

end ActuarialValuation
