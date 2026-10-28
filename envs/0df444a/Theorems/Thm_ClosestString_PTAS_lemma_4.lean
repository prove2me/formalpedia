-- Prove2me | Theorems.Thm_ClosestString_PTAS_lemma_4
-- name    : ClosestString.PTAS.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:17:35.547828+00:00
-- url     : https://prove2.me/theorems/10b9b613-67bb-47b9-8e49-7db5fb84c408
-- title:
--   Lemma 4 (Chernoff's bounds) — Pr(X > (1+δ)µ) < [e^δ/(1+δ)^{1+δ}]^µ and Pr(X < (1−δ)µ) ≤ exp(−µδ²/2)
-- statement:
--   Let $X_1,\dots,X_N$ be independent random 0-1 variables on a probability space, where $X_i$ takes the value $1$ with probability $p_i$, $0<p_i<1$. Let $X=\sum_{i=1}^NX_i$ and $\mu=\mathbb E[X]$. Then for every $\delta>0$:
--
--   1. $$\Pr\big(X>(1+\delta)\mu\big)<\left[\frac{e^{\delta}}{(1+\delta)^{1+\delta}}\right]^{\mu};$$
--   2. $$\Pr\big(X<(1-\delta)\mu\big)\le\exp\Big(-\tfrac12\mu\delta^2\Big).$$
--
--   These are the multiplicative Chernoff bounds the paper cites from Motwani and Raghavan (Theorems 4.2 and 4.3); Lemma 5 is derived from them.
--
--   **Formalization Note** The bounds are stated with the strict and non-strict signs exactly as printed; $\mu$ is the integral of $\sum_iX_i$.
--
--   Differences from the source:
--
--   - encoding: independent random 0-1 variables X_i taking 1 with probability p_i → measurable X_i : Ω → ℝ, iIndepFun, P(X_i = 1) = p_i and P(X_i = 0) = 1 − p_i; reason: the two point probabilities force X_i ∈ {0,1} almost surely; same instances
--   - encoding: n variables → N variables (Fin N); reason: n names the number of strings elsewhere in the mission; renaming only
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 5, Lemma 4 (citing Motwani–Raghavan, Randomized Algorithms, Theorems 4.2 and 4.3)

import Mathlib

namespace ClosestString.PTAS

open MeasureTheory ProbabilityTheory

/-- **Lemma 4** (Chernoff's bounds; Li, Ma & Wang, arXiv:cs/0002012v1, p. 5, citing
Motwani–Raghavan, Theorems 4.2 and 4.3): for independent 0-1 random variables `X_1, …, X_N` with
`P(X_i = 1) = p_i`, `0 < p_i < 1`, `X = Σ X_i` and `µ = E[X]`, for every `δ > 0`:
(1) `Pr(X > (1+δ)µ) < [e^δ/(1+δ)^{1+δ}]^µ`; (2) `Pr(X < (1−δ)µ) ≤ exp(−µδ²/2)`. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X Pr)
    (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hX_ber : ∀ i, Pr.real {ω | X i ω = 1} = p i ∧ Pr.real {ω | X i ω = 0} = 1 - p i)
    (δ : ℝ) (hδ : 0 < δ) :
    Pr.real {ω | (1 + δ) * (∫ ω', ∑ i, X i ω' ∂Pr) < ∑ i, X i ω} <
        (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (∫ ω', ∑ i, X i ω' ∂Pr) ∧
      Pr.real {ω | ∑ i, X i ω < (1 - δ) * (∫ ω', ∑ i, X i ω' ∂Pr)} ≤
        Real.exp (-(1 / 2) * (∫ ω', ∑ i, X i ω' ∂Pr) * δ ^ 2) := by sorry

end ClosestString.PTAS
