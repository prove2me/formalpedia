-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_lemma_B_1
-- name    : BudgetedAffine.Budget.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:48.311907+00:00
-- url     : https://prove2.me/theorems/b7ef3fed-6b35-4e86-afda-1496110fcf8c
-- title:
--   Lemma B.1 (Chernoff bound 1) — P(Ξ ≥ (1+δ)s) ≤ (e^δ/(1+δ)^{1+δ})^s for weighted Bernoulli sums
-- statement:
--   Let $\xi_1,\dots,\xi_r$ be independent Bernoulli trials with parameters $p_i\in[0,1]$, and let $\Xi=\sum_{i=1}^r\alpha_i\xi_i$ with $\alpha_1,\dots,\alpha_r\in[0,1]$. Let $s>0$ with $\mathbb E(\Xi)\le s$. Then for every $\delta>0$,
--   $$\mathbb P\big(\Xi\ge(1+\delta)s\big)\le\left(\frac{e^\delta}{(1+\delta)^{1+\delta}}\right)^s.$$
--
--   This variant of the Raghavan–Spencer inequality is the concentration bound behind Claim 3.2.
--
--   **Formalization Note** The probability and expectation are those of independent Bernoulli selection (the referenced definition `SpectralSparsify.Sampling.BernoulliSubset`): the outcome is the set $T$ of indices $i$ with $\xi_i=1$, so $\Xi=\sum_{i\in T}\alpha_i$. The powers are real powers.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma B.1, p. 32

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

namespace BudgetedAffine.Budget

open SpectralSparsify.Sampling

/-- Lemma B.1 (Chernoff bound 1): for independent Bernoulli `ξ₁, …, ξ_r` (parameters `pᵢ`; the
outcome is the set `T` of indices with `ξᵢ = 1`), `Ξ = ∑ αᵢ ξᵢ = ∑_{i ∈ T} αᵢ` with `αᵢ ∈ [0,1]`,
`s > 0` with `E(Ξ) ≤ s` and `δ > 0`: `P(Ξ ≥ (1 + δ) s) ≤ (e^δ / (1 + δ)^{1+δ})^s`. -/
theorem lemma_B_1 (r : ℕ) (p a : Fin r → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (s : ℝ) (hs : 0 < s)
    (hE : expect Finset.univ p (fun T => ∑ i ∈ T, a i) ≤ s) (δ : ℝ) (hδ : 0 < δ) :
    prob Finset.univ p (fun T => (1 + δ) * s ≤ ∑ i ∈ T, a i) ≤
      (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ s := by sorry

end BudgetedAffine.Budget
