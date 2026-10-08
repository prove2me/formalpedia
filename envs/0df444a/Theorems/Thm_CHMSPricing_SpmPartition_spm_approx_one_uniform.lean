-- Prove2me | Theorems.Thm_CHMSPricing_SpmPartition_spm_approx_one_uniform
-- name    : CHMSPricing.SpmPartition.spm_approx_one_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:44:17.721164+00:00
-- url     : https://prove2.me/theorems/43bb06d8-02a0-4997-a6ab-9d9f8d114f33
-- title:
--   Theorem 21, p. 15 — under a single unit (1-uniform matroid) the SPM S e/(e − 1)-approximates the optimal revenue
-- statement:
--   Consider $n$ single-parameter agents whose values $v_1,\dots,v_n$ for service are independent, $v_i\sim F_i$ with density $f_i$, and every $F_i$ is **regular** (its virtual value $\varphi_i(v)=v-\frac{1-F_i(v)}{f_i(v)}$ is non-decreasing). The seller may serve any set of agents allowed by a $1$-uniform matroid (a seller with one unit: at most one agent is served).
--
--   Let $M$ be any truthful (dominant-strategy incentive compatible, individually rational) mechanism for this constraint, with expected revenue $\mathcal R^M$, and let $q^M_i$ be the probability that $M$ serves agent $i$. Set the price $p_i=F_i^{-1}(1-q^M_i)$, so that agent $i$ accepts an offer at price $p_i$ with probability exactly $q^M_i$. The sequential posted-price mechanism $\mathcal S$ approaches the agents one at a time in decreasing order of their prices; it offers service to an agent at price $p_i$ whenever adding the agent to the set already served stays feasible, and the agent accepts iff $p_i\le v_i$. Write $\mathcal R^\sigma_{\mathbf p}$ for its expected revenue. Then
--
--   $$
--   \mathcal R^M\;\le\;\frac{e}{e-1}\,\mathcal R^\sigma_{\mathbf p}.
--   $$
--
--   This is the single-unit case of Theorem 6; the approximation factor $e/(e-1)\approx1.58$ improves the factor $2$ that holds for general matroids.
--
--   **Formalization Note** Values: each value distribution $F_i$ is given by a density $f_i$ that is measurable and strictly positive on a bounded interval $[\underline v_i,\bar v_i]$ with $0\le\underline v_i<\bar v_i$, integrates to $1$ there and puts no mass outside (the paper says only "distribution function $F_i$ with density $f_i$"). A truthful mechanism here is deterministic, dominant-strategy incentive compatible on the type space $\prod_i[\underline v_i,\bar v_i]$, ex-post individually rational, feasible on the type space, with measurable allocation events and measurable, integrable payments; payments of unserved agents are not forced to be zero. The prices are not computed by an inverse distribution function: they are arguments $p_i\in[\underline v_i,\bar v_i]$ with $F_i(p_i)=1-q^M_i$, which determines $p_i$ uniquely because $F_i$ is continuous and strictly increasing on the support. The ordering is a permutation $\sigma$ of $\{0,\dots,n-1\}$ with $\sigma(0)$ approached first; "decreasing order of their prices" is the hypothesis $a\le b\Rightarrow p_{\sigma(b)}\le p_{\sigma(a)}$, ties broken arbitrarily (the statement holds for every such $\sigma$). An agent accepts an offer iff $p_i\le v_i$. The statement is made for **every** truthful mechanism $M$, with the SPM built from $M$'s own service probabilities. Taking $M$ to be Myerson's mechanism gives the paper's statement, so this form is at least as strong; it follows from the same proof, since Lemma 2 and the rank bound hold for every truthful $M$ and Myerson's mechanism is never constructed. All distributions are assumed regular, as in the paper's analyses of §4 (the non-regular extension of Appendix E uses randomized prices and is not stated). The constant is exactly $e/(e-1)$, written `Real.exp 1 / (Real.exp 1 - 1)`.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 15, App. C.2, Theorem 21

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace CHMSPricing.SpmPartition

theorem spm_approx_one_uniform {n : ℕ}
    (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (M : Mechanism (Fin n)) (hM : IsTruthful D (uniformSystem (Fin n) 1) M)
    (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    revenue D M ≤ Real.exp 1 / (Real.exp 1 - 1) * spmRevenue D (uniformSystem (Fin n) 1) σ p := by sorry

end CHMSPricing.SpmPartition
