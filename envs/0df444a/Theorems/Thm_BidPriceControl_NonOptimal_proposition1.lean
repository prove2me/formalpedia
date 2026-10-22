-- Prove2me | Theorems.Thm_BidPriceControl_NonOptimal_proposition1
-- name    : BidPriceControl.NonOptimal.proposition1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:15:36.650606+00:00
-- url     : https://prove2.me/theorems/43d50e4d-3313-49db-bf0a-d6a42121b35b
-- title:
--   Proposition 1 — J_k(x) is finite and the control (4) is optimal
-- statement:
--   Let $A$ be the seat matrix of a network with $m$ legs and $n$ itineraries, and let the request vectors $R_1, \dots, R_k$ have laws $F_1, \dots, F_k$ that are probability measures concentrated on $\mathcal{S}$ with finite first moments $\mathbb{E}|R_t^j| < \infty$. Let $J$ be the optimal expected revenue of the Bellman equations (2)–(3), and let $u^*$ be the control
--   $$u_t^{j*}(y, r^j) = \begin{cases} 1 & r^j \ge J_{t-1}(y) - J_{t-1}(y - A^j) \text{ and } A^j \le y,\\ 0 & \text{otherwise.}\end{cases} \tag{4}$$
--   Then:
--
--   1. $J_t(y)$ is finite for every $t \le k$ and every capacity $y$: the expectation defining it in (2) is that of an integrable random variable;
--   2. $u^*$ is an admissible control (every decision lies in $\mathcal{U}(y)$ and is a measurable function of the request) and its expected revenue from any capacity $y$ with $k$ periods to go is $V^{u^*}_k(y) = J_k(y)$;
--   3. every admissible control $u$ satisfies $V^u_k(y) \le J_k(y)$ for every $y$.
--
--   Together, (2) and (3) say that $J_k(y)$ is the maximum expected revenue over all admissible controls, and that it is attained by the threshold control (4): accept a request exactly when its fare covers the opportunity cost $J_{t-1}(y) - J_{t-1}(y - A^j)$ of the seats it uses.
--
--   **Formalization Note.** Controls are Markov: the decision may depend on the period, the remaining capacity and the whole request vector $r$. Admissibility includes measurability of each decision in $r$, which the paper leaves implicit in taking expectations. Read literally, (4) accepts every itinerary $j$ with $r^j = 0 \ge J_{t-1}(y) - J_{t-1}(y - A^j)$, which is not a unit vector; `optimalControl` accepts only the arriving request ($r^j > 0$), the least such $j$, which has the same expected revenue. "$J_k(x)$ is finite" is stated as integrability of the Bellman integrands, since a real number is always finite. No continuity of the fare distributions is assumed.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, pp. 1580–1581, Proposition 1 and eq. (4)

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model

namespace BidPriceControl.NonOptimal

open MeasureTheory

/-- Proposition 1 (pp. 1580–1581): if every request vector `R_t`, `t = 1, …, k`, has a law on `𝒮`
with finite first moments, then (i) `J_t(y)` is finite, i.e. the Bellman integrand of (2) is
integrable at every `t ≤ k` and every capacity `y`; (ii) the control `u*` of (4) is admissible and
attains `J_k(y)`; (iii) no admissible control earns more than `J_k(y)`. -/
theorem proposition1 {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ)) (k : ℕ)
    (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t)) :
    (∀ t < k, ∀ y : Fin m → ℕ, Integrable (bellmanIntegrand A F t y) (F (t + 1))) ∧
    IsAdmissible A (optimalControl A F) ∧
    (∀ y : Fin m → ℕ, controlValue A F (optimalControl A F) k y = optValue A F k y) ∧
    (∀ u : Control m n, IsAdmissible A u → ∀ y : Fin m → ℕ,
      controlValue A F u k y ≤ optValue A F k y) := by sorry

end BidPriceControl.NonOptimal
