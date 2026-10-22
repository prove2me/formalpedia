-- Prove2me | Theorems.Thm_BidPriceControl_NonOptimal_counterexample_values
-- name    : BidPriceControl.NonOptimal.counterexample_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:26:06.253666+00:00
-- url     : https://prove2.me/theorems/8a37ee1f-cedb-4903-a2a2-ff0d7cf22b83
-- title:
--   §3.1 — in the Table 1 instance, J_1(1,1) = 400, J_1 = 0 elsewhere, and J_2(1,1) = 440
-- statement:
--   In the instance of §3.1 and Table 1 (two legs, the through itinerary $(1,1)$ and the local itineraries $(1,0)$ and $(0,1)$; in period 2 a \$500 through request w.p. 0.4 and a \$250 request for each local itinerary w.p. 0.3; in period 1 a \$500 through request w.p. 0.8 and no request w.p. 0.2), the optimal expected revenues of the Bellman equations (2)–(3) are
--   $$J_1(1,1) = 400, \qquad J_1(1,0) = J_1(0,1) = J_1(0,0) = 0, \qquad J_2(1,1) = 440.$$
--
--   With one period left and a seat on each leg, the through request is worth $0.8 \cdot 500 = 400$; once either leg is sold out it can no longer be served. With two periods left, the optimal expected revenue is \$440.
--
--   **Formalization Note.** $J$ is `optValue` for the seat matrix `ceA` and the laws `ceLaw`; `ceX = (1,1)`. All numbers are exact reals.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1582, §3.1, first paragraph

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model
import Definitions.Def_BidPriceControl_NonOptimal_CounterExample

namespace BidPriceControl.NonOptimal

open MeasureTheory

/-- The values of the dynamic program (2)–(3) in the instance of §3.1 (p. 1582): with one period
to go, `J_1(1,1) = 400` (the through request, $500 w.p. 0.8) and `J_1(y) = 0` at the other three
capacities, where the through itinerary no longer fits; with two periods to go and one seat on each
leg, the optimal expected revenue is `J_2(1,1) = 440`. -/
theorem counterexample_values :
    optValue ceA ceLaw 1 ![1, 1] = 400 ∧ optValue ceA ceLaw 1 ![1, 0] = 0 ∧
    optValue ceA ceLaw 1 ![0, 1] = 0 ∧ optValue ceA ceLaw 1 ![0, 0] = 0 ∧
    optValue ceA ceLaw 2 ceX = 440 := by sorry

end BidPriceControl.NonOptimal
