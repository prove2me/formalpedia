-- Prove2me | Theorems.Thm_DynAssortPers_TypeDist_display_p44_hoeffding
-- name    : DynAssortPers.TypeDist.display_p44_hoeffding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:50.066992+00:00
-- url     : https://prove2.me/theorems/13260fc6-46bd-4e60-8dac-57adfb5f67df
-- title:
--   Proof of Theorem 4, p. 44 — $\mathbb P(\|\hat\mu-\mu^\star\|_q>\eta)\le\sum_i\mathbb P(|\hat\mu_i-\mu^\star_i|>\eta/m^{1/q})\le 2m\exp(-2N\eta^2/m^{2/q})$
-- statement:
--   Let $\mu^\star\in\Delta^m$ be the customer type distribution, let $i_1,\dots,i_N$ ($N\ge1$) be i.i.d. draws from $\mu^\star$, and let $\hat\mu_i=\frac1N\sum_{t=1}^N\mathbb I[i_t=i]$ be the empirical type frequencies. Let $q\in[1,\infty]$ and $\eta\ge0$. Then
--
--   $$\mathbb P\big(\|\hat\mu-\mu^\star\|_q>\eta\big)\ \le\ \sum_{i=1}^m\mathbb P\big(|\hat\mu_i-\mu^\star_i|>\eta/m^{1/q}\big)\ \le\ 2m\exp\!\big(-2N\eta^2/m^{2/q}\big),$$
--
--   with $m^{1/q}=m^{2/q}=1$ when $q=\infty$.
--
--   The first inequality is a union bound over the coordinates, the second a per-coordinate tail bound for an average of $N$ Bernoulli indicators. Setting the right-hand side equal to $e^{-\tau}$ gives the second term in the minimum of Theorem 4.
--
--   **Formalization Note** The paper prints $2m\exp(-2n\eta^2/m^{2/q})$; $n$ (the number of items) is a typo for the sample size $N$, which is what the Hoeffding step produces and what Theorem 4 requires, so the statement uses $N$. The paper leaves the range of $\eta$ implicit; $\eta\ge0$ is assumed, because for $\eta<0$ the left side equals $1$ while the right side can be smaller. Probabilities are finite sums over samples `Fin N → Fin m` weighted by $\prod_t\mu^\star_{x_t}$; restricting the observations $(i_t,j_t,S_t)$ to their types is exact, since the types are i.i.d. $\mu^\star$ whatever the items and assortments do. Types are 0-based.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 4, p. 44, first display (after "By union bound and Hoeffding's inequality")

import Mathlib
import Definitions.Def_DynAssortPers_TypeDist_IIDSampling
import Definitions.Def_DynAssortPers_TypeDist_Estimator

namespace DynAssortPers.TypeDist

open Finset
open scoped ENNReal

theorem display_p44_hoeffding {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (hN : 0 < N) (q : ℝ≥0∞) (hq : 1 ≤ q) (η : ℝ) (hη : 0 ≤ η) :
    iidProb μ (fun x : Fin N → Fin m => η < lqNorm q (fun i => muHat x i - μ i))
        ≤ ∑ i : Fin m, iidProb μ (fun x : Fin N → Fin m =>
            η / (m : ℝ) ^ invQ q < |muHat x i - μ i|) ∧
      ∑ i : Fin m, iidProb μ (fun x : Fin N → Fin m =>
            η / (m : ℝ) ^ invQ q < |muHat x i - μ i|)
        ≤ 2 * m * Real.exp (-2 * N * η ^ 2 / (m : ℝ) ^ (2 * invQ q)) := by sorry

end DynAssortPers.TypeDist
