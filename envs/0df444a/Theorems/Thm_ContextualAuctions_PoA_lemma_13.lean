-- Prove2me | Theorems.Thm_ContextualAuctions_PoA_lemma_13
-- name    : ContextualAuctions.PoA.lemma_13
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T06:35:56.191577+00:00
-- url     : https://prove2.me/theorems/6e0fe3fa-8c6b-43a6-9310-9fcd994fa547
-- title:
--   Lemma 13, p. ec19 — equilibrium liquid value dominates any allocation's minus second-price payments
-- statement:
--   Consider a contextual standard auction with zero reserve prices ($r(\alpha)=0$ on the item set $A$). Let $\mu$ be a pacing equilibrium, i.e. $\mu\in X_0$ and $\mu\in C_0^*(\mu)$. Let $x^\mu$ be its highest-bid allocation (ties split evenly) and let $x$ be any measurable fractional allocation. Write $p(\alpha,\tilde\theta)$ for the second-highest paced value $w_j^\top\alpha/(1+\mu(w_j,B_j))$ among the $n$ buyers. Fix a buyer $i$. Then for $G$-almost every type $\theta_i=(w_i,B_i)$,
--   $$
--   \min\Big\{\mathbb E_{\alpha,\theta_{-i}}\big[w_i^\top\alpha\cdot x^\mu_i(\alpha,\theta_i,\theta_{-i})\big],\,B_i\Big\}
--   \;\ge\;
--   \min\Big\{\mathbb E_{\alpha,\theta_{-i}}\big[w_i^\top\alpha\cdot x_i(\alpha,\theta_i,\theta_{-i})\big],\,B_i\Big\}
--   -\mathbb E_{\alpha,\theta_{-i}}\big[p(\alpha,\theta_i,\theta_{-i})\,x_i(\alpha,\theta_i,\theta_{-i})\big].
--   $$
--   The expectations are over $\alpha\sim F$ and the other buyers' types drawn i.i.d. from $G$.
--
--   This is the per-type inequality behind the price-of-anarchy bound. In equilibrium, each buyer type's capped value is at least its capped value under any other allocation, minus the second-price payments that allocation would collect from it. Summing over buyers and types turns it into Theorem 3.
--
--   **Formalization Note** The paper states the lemma for every $\theta_i\in\Theta$, using that $\mu(\theta_i)$ minimizes the buyer's dual function. Here the equilibrium hypothesis is the fixed-point condition $\mu\in C_0^*(\mu)$ on $X_0$, which pins down $\mu$ only up to $G$-null sets, so the conclusion is stated $G$-almost everywhere. $x^\mu$ is the platform's highest-bid allocation under the first-price value-pacing bids $\beta^\mu$. By revenue equivalence (Theorem 2) it coincides with the second-price allocation used in the paper. The expectations are written as integrals over $F\otimes G^{n}$ with coordinate $i$ overwritten by $\theta_i$ (`inner`, `interimPrice`).
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science (2023), doi:10.1287/mnsc.2023.4719; arXiv:2102.10476, Appendix D, Lemma 13 (p. ec19), in the proof of Theorem 3

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_SecondPrice

namespace ContextualAuctions.PoA

open MeasureTheory

/-- Lemma 13, printed p. ec19: per-type liquid-value comparison with the second-price term. -/
theorem lemma_13 (M : Model) (hM : M.Standing)
    (hr : ∀ α ∈ M.A, M.r α = 0)
    (μ : Buyer M → ℝ) (hμ : μ ∈ X0 M) (hfix : μ ∈ C0star M μ)
    (x : Allocation M) (hx : IsAllocation M x) (i : Fin M.n) :
    ∀ᵐ θi ∂M.G,
      min (ContextualAuctions.PoA.inner M x i θi) θi.2 - interimPrice M μ x i θi ≤
        min (ContextualAuctions.PoA.inner M (xmu M μ) i θi) θi.2 := by sorry

end ContextualAuctions.PoA
