-- Prove2me | Theorems.Thm_DynAssortPers_TypeDist_theorem_4
-- name    : DynAssortPers.TypeDist.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:49.909484+00:00
-- url     : https://prove2.me/theorems/9a619b69-1de8-439c-b218-bfa7b9b3a122
-- title:
--   Theorem 4 — w.p. $\ge1-e^{-\tau}$, $\|\hat\mu-\mu^\star\|_q\le\min\{8\sqrt{(\tau+m)/N},\ \frac{m^{1/q}}{\sqrt2}\sqrt{(\tau+\log(2m))/N}\}$
-- statement:
--   Let $\mu^\star\in\Delta^m$ be a distribution of customer types on $\{1,\dots,m\}$, and let $i_1,\dots,i_N$ ($N\ge1$) be the types of $N$ customers, drawn i.i.d. from $\mu^\star$. Let
--   $$\hat\mu_i=\frac1N\sum_{t=1}^N\mathbb I[i_t=i]$$
--   be the empirical type frequencies. Let $\tau\ge0$ and $q\in[1,\infty]$ be given. Then, with probability at least $1-e^{-\tau}$,
--
--   $$\|\hat\mu-\mu^\star\|_q\ \le\ \min\left\{8\sqrt{\frac{\tau+m}{N}},\ \frac{m^{1/q}}{\sqrt2}\sqrt{\frac{\tau+\log(2m)}{N}}\right\},$$
--
--   where $\|\cdot\|_q$ is the $\ell_q$ norm on $\mathbb R^m$, $m^{1/q}=1$ for $q=\infty$, and $\log$ is the natural logarithm.
--
--   The first term shows that $\mu^\star$ is estimated consistently in every $\ell_q$ norm, $q\ge1$, as soon as $N$ grows faster than $m$; in particular $\hat\mu$ is $\sqrt{m/N}$-consistent in $\ell_1$. The second term is the sharper bound when $N$ is large compared with $m^{2/q}$.
--
--   **Formalization Note** $N\ge1$ is assumed: $\hat\mu$ is undefined for an empty sample. $m\ge1$ is implied by $\mu^\star\in\Delta^m$. The probability is the finite sum, over the samples $x\in\{1,\dots,m\}^N$ in the event, of $\prod_t\mu^\star_{x_t}$. The paper's observation model also records an item $j_t$ and an assortment $S_t$ with every type; since the types $i_t$ are i.i.d. $\mu^\star$ whatever the items and assortments are, the type marginal is the whole law of $\hat\mu$, and restricting to it is exact. The $\ell_q$ norm is Mathlib's `PiLp` norm; $m^{1/q}$ is $m$ raised to an exponent defined as $0$ at $q=\infty$ and $1/q$ otherwise. Types are 0-based.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Theorem 4, Sec. 3.2.4, p. 18

import Mathlib
import Definitions.Def_DynAssortPers_TypeDist_IIDSampling
import Definitions.Def_DynAssortPers_TypeDist_Estimator

namespace DynAssortPers.TypeDist

open Finset
open scoped ENNReal

theorem theorem_4 {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (hN : 0 < N) (τ : ℝ) (hτ : 0 ≤ τ) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    1 - Real.exp (-τ) ≤
      iidProb μ (fun x : Fin N → Fin m =>
        lqNorm q (fun i => muHat x i - μ i)
          ≤ min (8 * Real.sqrt ((τ + m) / N))
                ((m : ℝ) ^ invQ q / Real.sqrt 2 * Real.sqrt ((τ + Real.log (2 * m)) / N))) := by sorry

end DynAssortPers.TypeDist
