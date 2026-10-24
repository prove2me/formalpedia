-- Prove2me | Theorems.Thm_ContextualAuctions_PoA_price_le_liquid_value
-- name    : ContextualAuctions.PoA.price_le_liquid_value
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T06:35:54.690786+00:00
-- url     : https://prove2.me/theorems/f2a20320-d2d4-4706-85ed-427757dacce4
-- title:
--   Proof of Theorem 3, (D-10) — equilibrium second-price payment is at most liquid value
-- statement:
--   Consider a contextual standard auction with zero reserve prices ($r(\alpha)=0$ on the item set $A$). Let $\mu$ be a pacing equilibrium, i.e. $\mu\in X_0$ and $\mu\in C_0^*(\mu)$, with highest-bid allocation $x^\mu$. Let $p(\alpha,\tilde\theta)$ be the second-highest paced value $w_j^\top\alpha/(1+\mu(w_j,B_j))$ among the $n$ buyers. Fix a buyer $i$. Then for $G$-almost every type $\theta_i=(w_i,B_i)$,
--   $$
--   \mathbb E_{\alpha,\theta_{-i}}\big[p(\alpha,\theta_i,\theta_{-i})\,x^\mu_i(\alpha,\theta_i,\theta_{-i})\big]
--   \;\le\;
--   \min\Big\{\mathbb E_{\alpha,\theta_{-i}}\big[w_i^\top\alpha\cdot x^\mu_i(\alpha,\theta_i,\theta_{-i})\big],\,B_i\Big\}.
--   $$
--   The expectations are over $\alpha\sim F$ and the other buyers' types drawn i.i.d. from $G$.
--
--   In words, the equilibrium second-price expenditure of each buyer type is at most its liquid value. It is at most the budget because the pacing-based equilibrium strategy is budget-feasible. It is at most the value because a winning buyer's paced value, and hence its value, is at least the second-highest paced value. This is the last inequality of display (D-10) in the proof of Theorem 3. It shows that the equilibrium revenue is at most the equilibrium liquid welfare.
--
--   **Formalization Note** The paper asserts this for every type, from the dual optimality of $\mu(\theta_i)$. The fixed-point hypothesis determines $\mu$ only up to $G$-null sets, so the statement is $G$-almost everywhere. $x^\mu$ is the platform's highest-bid allocation under the first-price value-pacing bids $\beta^\mu$, which by revenue equivalence agrees with the second-price allocation of the paper.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science (2023), doi:10.1287/mnsc.2023.4719; arXiv:2102.10476, Appendix D, Proof of Theorem 3, display (D-10), last inequality and the sentence following it (p. ec21)

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_SecondPrice

namespace ContextualAuctions.PoA

open MeasureTheory

/-- Proof of Theorem 3, display (D-10), last inequality, printed p. ec21: in equilibrium the
interim second-price payment of every type is at most its liquid value. -/
theorem price_le_liquid_value (M : Model) (hM : M.Standing)
    (hr : ∀ α ∈ M.A, M.r α = 0)
    (μ : Buyer M → ℝ) (hμ : μ ∈ X0 M) (hfix : μ ∈ C0star M μ) (i : Fin M.n) :
    ∀ᵐ θi ∂M.G,
      interimPrice M μ (xmu M μ) i θi ≤
        min (ContextualAuctions.PoA.inner M (xmu M μ) i θi) θi.2 := by sorry

end ContextualAuctions.PoA
