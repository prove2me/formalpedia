-- Prove2me | Theorems.Thm_BidPriceControl_NonOptimal_no_bid_price_optimal_decision
-- name    : BidPriceControl.NonOptimal.no_bid_price_optimal_decision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:26:26.75421+00:00
-- url     : https://prove2.me/theorems/29f6b9c6-7df0-4b07-bad8-0b5de4e885fb
-- title:
--   §3.1 — no bid prices reproduce the optimal decisions in period 2 (μ_1 > 250, μ_2 > 250, μ_1 + μ_2 ≤ 500 is impossible)
-- statement:
--   In the instance of §3.1 and Table 1, with capacity $(1,1)$ and two periods to go, call an admissible control $u$ **optimal** if its expected revenue $V^u_2(1,1)$ is at least that of every admissible control. Then for every family of bid prices $\mu_t(y) \in \mathbb{R}^2$ (arbitrary real values, depending on the period and on the capacity) there is a period-2 request $r$ with positive probability under $F_2$ at which the decision of the bid-price control of Definition 1 at capacity $(1,1)$ differs from the decision of every optimal control:
--   $$\forall \mu\ \exists r,\ F_2(\{r\}) > 0 \ \text{ and }\ \forall u \text{ optimal},\quad u^{\mu}_2\big((1,1), r\big) \ne u_2\big((1,1), r\big).$$
--
--   An optimal control accepts the through request and rejects both local requests in period 2; a bid-price control would need $\mu_1 > 250$, $\mu_2 > 250$ and $\mu_1 + \mu_2 \le 500$, which is impossible. So no bid-price policy produces an optimal decision in period 2.
--
--   **Formalization Note.** Decisions are compared as elements of `Option (Fin 3)` (`none` = reject). Optimality is expressed through the expected revenue of admissible controls, not through the values $J$, so the statement does not depend on how the dynamic program is encoded. The request $r$ is one of the three atoms of $F_2$; which one depends on $\mu$.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1582, §3.1, second paragraph

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model
import Definitions.Def_BidPriceControl_NonOptimal_CounterExample

namespace BidPriceControl.NonOptimal

open MeasureTheory

/-- §3.1 (p. 1582): no bid-price policy can produce an optimal decision in period 2. For every
family of bid prices `μ` there is a period-2 request `r` that arrives with positive probability at
which the bid-price control's decision at the initial capacity `(1, 1)` differs from the decision
of every optimal admissible control (one whose expected revenue from `(1, 1)` with two periods to
go is at least that of every admissible control). -/
theorem no_bid_price_optimal_decision (μ : ℕ → (Fin 2 → ℕ) → Fin 2 → ℝ) :
    ∃ r : Fin 3 → ℝ, ceLaw 2 {r} ≠ 0 ∧
      ∀ u : Control 2 3, IsAdmissible ceA u →
        (∀ v : Control 2 3, IsAdmissible ceA v →
          controlValue ceA ceLaw v 2 ceX ≤ controlValue ceA ceLaw u 2 ceX) →
        bidPriceControl ceA μ 2 ceX r ≠ u 2 ceX r := by sorry

end BidPriceControl.NonOptimal
