-- Prove2me | Theorems.Thm_ActuarialValuation_ulUnallocated_nonneg
-- name    : ActuarialValuation.ulUnallocated_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:03:13.561913+00:00
-- url     : https://prove2.me/theorems/de1c0fd3-b0e0-4f30-9fd7-6d085f06152f
-- title:
--   Premium allocation, bid and offer prices and fund charges: ulUnallocated_nonneg
-- statement:
--   Allocation rates no greater than one cannot generate negative retained premiums. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulUnallocated

namespace ActuarialValuation

theorem ulUnallocated_nonneg (premium rate : ℝ) (hp : 0≤premium) (hr0 : 0≤rate) (hr1 : rate≤1) : 0≤ulUnallocated premium rate := by sorry

end ActuarialValuation
