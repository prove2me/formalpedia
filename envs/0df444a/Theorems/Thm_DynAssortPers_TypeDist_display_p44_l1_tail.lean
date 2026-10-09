-- Prove2me | Theorems.Thm_DynAssortPers_TypeDist_display_p44_l1_tail
-- name    : DynAssortPers.TypeDist.display_p44_l1_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:25.28124+00:00
-- url     : https://prove2.me/theorems/12d23878-5e02-448c-8dd9-133359793948
-- title:
--   Proof of Theorem 4, p. 44 — $\mathbb P(\|\mu^\star-\hat\mu\|_1>\eta)\le e^{m-N\eta^2/64}$
-- statement:
--   Let $\mu^\star\in\Delta^m$, let $i_1,\dots,i_N$ ($N\ge1$) be i.i.d. draws from $\mu^\star$, and let $\hat\mu$ be the empirical type frequencies. For every $\eta\ge0$,
--
--   $$\mathbb P\big(\|\mu^\star-\hat\mu\|_1>\eta\big)\ \le\ e^{\,m-N\eta^2/64},\qquad \|\mu^\star-\hat\mu\|_1=\sum_{i=1}^m|\mu^\star_i-\hat\mu_i|.$$
--
--   The bound is nontrivial only for $\eta>8\sqrt{m/N}$, and it is dimension-sensitive only through $m$ in the exponent. Setting the right-hand side equal to $e^{-\tau}$ gives the first term $8\sqrt{(\tau+m)/N}$ in the minimum of Theorem 4, for $q=1$ and hence for every $q\ge1$.
--
--   **Formalization Note** $\eta\ge0$ is assumed; the paper leaves the range of $\eta$ implicit, and for $\eta<0$ the left side equals $1$ while the right side can be smaller. The $\ell_1$ norm is written as the sum of absolute coordinates. Probabilities are finite sums over samples `Fin N → Fin m` weighted by $\prod_t\mu^\star_{x_t}$; only the types of the observations enter. Types are 0-based.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 4, p. 44, display after "Therefore, using the concavity of square root, we have that"

import Mathlib
import Definitions.Def_DynAssortPers_TypeDist_IIDSampling
import Definitions.Def_DynAssortPers_TypeDist_Estimator

namespace DynAssortPers.TypeDist

open Finset

theorem display_p44_l1_tail {m N : ℕ} (μ : Fin m → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin m))
    (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η) :
    iidProb μ (fun x : Fin N → Fin m => η < ∑ i, |μ i - muHat x i|)
      ≤ Real.exp (m - N * η ^ 2 / 64) := by sorry

end DynAssortPers.TypeDist
