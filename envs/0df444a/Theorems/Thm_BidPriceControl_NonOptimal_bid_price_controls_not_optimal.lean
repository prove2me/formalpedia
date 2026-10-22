-- Prove2me | Theorems.Thm_BidPriceControl_NonOptimal_bid_price_controls_not_optimal
-- name    : BidPriceControl.NonOptimal.bid_price_controls_not_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:27:01.241717+00:00
-- url     : https://prove2.me/theorems/bc375958-0611-4837-9e41-a72799611e1e
-- title:
--   §3.1 counterexample — optimal expected revenue $440, best bid-price control $400
-- statement:
--   Consider the network of §3.1 and Table 1: two legs with one seat each, the through itinerary $(1,1)$ and the local itineraries $(1,0)$ and $(0,1)$, and two periods to go. In period 2 a through request with fare \$500 arrives with probability 0.4 and a request for each local itinerary with fare \$250 with probability 0.3; in period 1 a through request with fare \$500 arrives with probability 0.8 and nothing arrives with probability 0.2. For an admissible control $u$ let $V^u_2(1,1)$ be its expected revenue, and for bid prices $\mu$ let $u^\mu$ be the bid-price control of Definition 1. Then
--   $$\max_{u \text{ admissible}} V^u_2(1,1) = 440 \qquad\text{and}\qquad \max_{\mu} V^{u^\mu}_2(1,1) = 400,$$
--   both maxima being attained: some admissible control earns exactly 440 and none earns more, some bid prices earn exactly 400 and none earn more.
--
--   The optimal policy thus earns 10% more expected revenue than the best bid-price policy, so bid-price controls are not optimal in general, even though Proposition 1 shows that the optimal policy compares each fare with an opportunity cost.
--
--   **Formalization Note.** The maximum over bid-price controls ranges over *all* real bid prices $\mu_t^i(y)$, positive or negative, depending on the period and the remaining capacity; the maximum over admissible controls ranges over all Markov controls whose decisions lie in $\mathcal{U}(y)$ and are measurable in the request. A bid-price control accepts only the arriving request, at most one itinerary per period. The instance has deterministic fares, which the paper notes violates its continuity assumption; continuity is not assumed anywhere in this mission.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, pp. 1581–1582, §3.1 (counterexample to bid-price optimality) and Table 1

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model
import Definitions.Def_BidPriceControl_NonOptimal_CounterExample

namespace BidPriceControl.NonOptimal

open MeasureTheory

/-- The counterexample of §3.1 (pp. 1581–1582): in the two-leg, two-period instance of Table 1
with one seat on each leg, the optimal expected revenue over all admissible controls is $440, and
it is attained, while the best bid-price control (Definition 1, with arbitrary real bid prices
depending on time and capacity) earns exactly $400. -/
theorem bid_price_controls_not_optimal :
    (∃ u : Control 2 3, IsAdmissible ceA u ∧ controlValue ceA ceLaw u 2 ceX = 440) ∧
    (∀ u : Control 2 3, IsAdmissible ceA u → controlValue ceA ceLaw u 2 ceX ≤ 440) ∧
    IsGreatest {v : ℝ | ∃ μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ,
      v = controlValue ceA ceLaw (bidPriceControl ceA μ) 2 ceX} 400 := by sorry

end BidPriceControl.NonOptimal
