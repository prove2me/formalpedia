-- Prove2me | Theorems.Thm_DynamicAssortment_Separation_choice_probabilities_sum_to_one
-- name    : DynamicAssortment.Separation.choice_probabilities_sum_to_one
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T10:23:55.493819+00:00
-- url     : https://prove2.me/theorems/7eb221c5-207c-410e-9a53-45633476bc94
-- title:
--   The choice probabilities $p_i(S,\mu)$, $i\in S$, and $p_0(S,\mu)$ sum to one
-- statement:
--   Consider the random-utility choice model of Sauré–Zeevi (§3.2): a customer facing an assortment $S\subseteq\{1,\dots,N\}$ has utilities $U_i=\mu_i+\zeta_i$ for $i\in S$ and $U_0=\zeta_0$ for the no-purchase option ($\mu_0=0$), where the shocks $\zeta_0,\zeta_i$ are i.i.d. with a density $f$ that is integrable, everywhere positive and integrates to $1$. Writing $F(x)=\int_{-\infty}^x f$, the probability that product $i\in S$ is chosen is
--   $$p_i(S,\mu)=\int_{\mathbb R}\Big(\prod_{j\in S\setminus\{i\}}F(x-\mu_j)\Big)F(x)\,f(x-\mu_i)\,dx,$$
--   and the no-purchase probability is
--   $$p_0(S,\mu)=\int_{\mathbb R}\Big(\prod_{j\in S}F(x-\mu_j)\Big)f(x)\,dx .$$
--
--   **Claim.** These numbers form a probability distribution on $S\cup\{0\}$: for every finite $S$ and every $\mu\in\mathbb R^N$,
--   $$\sum_{i\in S}p_i(S,\mu)+p_0(S,\mu)=1 .$$
--
--   Probabilistically, $p_k$ is the probability that alternative $k$ has the largest utility, and ties have probability zero because the utilities have densities. Analytically, the integrand of the sum is the a.e. derivative of $x\mapsto\prod_{k\in S\cup\{0\}}F(x-\mu_k)$, which increases from $0$ to $1$.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 391, §3.2 (choice probabilities p_i(S, μ) of the random-utility model, a distribution over S ∪ {0}); used implicitly in the proof of Theorem 2 (App. A, pp. 402–403) whenever probabilities are bounded by one

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel

namespace DynamicAssortment.Separation

/-- The choice probabilities of the random-utility model (p. 391, §3.2) form a probability
distribution on `S ∪ {0}`: `∑_{i ∈ S} p_i(S, μ) + p_0(S, μ) = 1` for every assortment `S` and
every mean-utility vector `μ`, when the shocks have a density. -/
theorem choice_probabilities_sum_to_one {N : ℕ} (f : ℝ → ℝ) (hf : IsNoiseDensity f)
    (μ : Fin N → ℝ) (S : Finset (Fin N)) :
    ∑ i ∈ S, choiceProb f μ S i + noPurchaseProb f μ S = 1 := by sorry

end DynamicAssortment.Separation
