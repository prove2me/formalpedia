-- Prove2me | Theorems.Thm_CrossSell_Pricing_optimal_price
-- name    : CrossSell.Pricing.optimal_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:15.445458+00:00
-- url     : https://prove2.me/theorems/2170706b-d399-451c-9ff0-90da06fa0cd7
-- title:
--   p. 13, by the proof of Theorem 1 — the prices p*_i = z* + c_i − t*_i + 1 with r* maximizing H(r; z*) attain z*, and no prices earn more
-- statement:
--   In the sequential multinomial logit model (main offer set $S$, secondary sets $T_i$, utilities $u_i, v_{il}$, costs $c_i, s_l$, finitely many secondary products), let $z^*$ be a fixed point of $H$, i.e. $z^* = H(z^*) = \sup_{\mathbf r} H(\mathbf r; z^*)$, and let $\mathbf r^*$ be a maximizer of $\mathbf r \mapsto H(\mathbf r; z^*)$. Write $t_i^* = t_i(\mathbf r^*)$ for the secondary profit of $T_i$ at prices $\mathbf r^*$ and set
--   $$p_i^* = z^* + c_i - t_i^* + 1 \qquad (i \in \mathcal M).$$
--   Then
--   $$\Pi(S,\mathbf T,\mathbf p^*,\mathbf r^*) = z^* \qquad\text{and}\qquad \Pi(S,\mathbf T,\mathbf p,\mathbf r) \le z^* \ \text{ for all } \mathbf p, \mathbf r.$$
--
--   In words, $(\mathbf p^*, \mathbf r^*)$ is an optimal joint price vector and $z^*$ is the optimal total profit. This is the explicit price formula the paper derives "by the proof of Theorem 1"; it reduces the joint pricing problem to the secondary-price problem $\max_{\mathbf r} H(\mathbf r; z^*)$ and a scalar fixed point.
--
--   **Formalization Note.** The prices $p_i^*$ are defined on all of $\mathcal M$; only those with $i \in S$ affect the profit. The maximizer $\mathbf r^*$ is a hypothesis, as on the page ("$\mathbf r^*$ is the solution to the pricing problem … $\max_{\mathbf r} H(\mathbf r; z^*)$").
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 13, paragraph after Proposition 1 ("By the proof of Theorem 1, the optimal price for main product i is …")

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem optimal_price {ι κ : Type*} [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) (zstar : ℝ) (rstar : κ → ℝ)
    (hz : zstar = Hmax S T u c s v zstar)
    (hr : ∀ r : κ → ℝ, Hr S T u c s v r zstar ≤ Hr S T u c s v rstar zstar) :
    profit S T u c s v (fun i => zstar + c i - secProfit T s v rstar (some i) + 1) rstar = zstar ∧
    ∀ (p : ι → ℝ) (r : κ → ℝ), profit S T u c s v p r ≤ zstar := by sorry

end CrossSell.Pricing
