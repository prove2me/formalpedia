-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_lemma_B_2
-- name    : BudgetedAffine.Budget.lemma_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:29.098274+00:00
-- url     : https://prove2.me/theorems/4b3e6adb-d50c-48a9-a7a7-b130c0c14e98
-- title:
--   Lemma B.2 (Chernoff bound 2) — P(Ξ > (1−δ)μ) ≥ 1 − e^{−δ²μ/2}
-- statement:
--   Let $\xi_1,\dots,\xi_r$ be independent Bernoulli trials with parameters $p_i\in[0,1]$, and let
--   $$\Xi=\lambda+\sum_{i=1}^r\alpha_i\xi_i$$
--   with $\lambda\ge0$ and $\alpha_1,\dots,\alpha_r\in(0,1]$. Let $\mu=\mathbb E(\Xi)$. Then for every $0<\delta<1$,
--   $$\mathbb P\big(\Xi>(1-\delta)\mu\big)\ge1-e^{-\delta^2\mu/2}.$$
--
--   This lower-tail bound is used in Claim 3.3.
--
--   **Formalization Note** Probabilities are those of independent Bernoulli selection (the referenced definition `SpectralSparsify.Sampling.BernoulliSubset`), the outcome being the set $T$ of indices with $\xi_i=1$. The paper prints a strict inequality $\mathbb P(\Xi>(1-\delta)\mu)>1-e^{-\delta^2\mu/2}$, which is false when $\mu=0$ (e.g. $\lambda=0$ and every $p_i=0$: both sides are $0$). The statement here is the non-strict form, which is what the paper's proof establishes ("we show equivalently that $\mathbb P(\Xi\le(1-\delta)\mu)\le e^{-\delta^2\mu/2}$") and what Claim 3.3 uses.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma B.2, p. 33

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

namespace BudgetedAffine.Budget

open SpectralSparsify.Sampling

/-- Lemma B.2 (Chernoff bound 2), in the non-strict form its proof establishes: for independent
Bernoulli `ξ₁, …, ξ_r` (parameters `pᵢ`; the outcome is the set `T` of indices with `ξᵢ = 1`),
`Ξ = λ + ∑ αᵢ ξᵢ = λ + ∑_{i ∈ T} αᵢ` with `λ ≥ 0`, `αᵢ ∈ (0,1]`, `μ = E(Ξ)` and `0 < δ < 1`:
`P(Ξ > (1 − δ) μ) ≥ 1 − e^{−δ²μ/2}`. -/
theorem lemma_B_2 (r : ℕ) (p a : Fin r → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (ha : ∀ i, 0 < a i ∧ a i ≤ 1) (lam : ℝ) (hlam : 0 ≤ lam) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    1 - Real.exp (-(δ ^ 2 * expect Finset.univ p (fun T => lam + ∑ i ∈ T, a i) / 2)) ≤
      prob Finset.univ p (fun T =>
        (1 - δ) * expect Finset.univ p (fun T' => lam + ∑ i ∈ T', a i) < lam + ∑ i ∈ T, a i) := by sorry

end BudgetedAffine.Budget
