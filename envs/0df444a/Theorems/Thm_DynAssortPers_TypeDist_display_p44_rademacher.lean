-- Prove2me | Theorems.Thm_DynAssortPers_TypeDist_display_p44_rademacher
-- name    : DynAssortPers.TypeDist.display_p44_rademacher
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:51.517825+00:00
-- url     : https://prove2.me/theorems/3c48378f-ca67-4667-ad82-da14f3c27b5b
-- title:
--   Proof of Theorem 4, p. 44 — $\widehat{\mathfrak R}_N=\frac1N\sum_i\frac1{2^N}\sum_\epsilon|\sum_t\mathbb I[i_t=i]\epsilon_t|\le\frac1{\sqrt N}\sum_i\sqrt{\hat\mu_i}\le\sqrt{m/N}$
-- statement:
--   Fix any sample of types $i_1,\dots,i_N\in\{1,\dots,m\}$ with $N\ge1$, let $\hat\mu$ be its empirical type frequencies and $I_t=e_{i_t}$. The empirical Rademacher complexity
--   $$\widehat{\mathfrak R}_N=\frac1{2^N}\sum_{\epsilon\in\{-1,+1\}^N}\ \sup_{\|v\|_\infty\le1}\ \frac1N\sum_{t=1}^N\epsilon_t\,v^TI_t$$
--   satisfies the chain
--
--   $$\begin{aligned}
--   \widehat{\mathfrak R}_N
--   &=\frac1{2^N}\sum_{\epsilon\in\{-1,+1\}^N}\Big\|\frac1N\sum_{t=1}^N\epsilon_tI_t\Big\|_1
--   =\frac1N\sum_{i=1}^m\frac1{2^N}\sum_{\epsilon\in\{-1,+1\}^N}\Big|\sum_{t=1}^N\mathbb I[i_t=i]\,\epsilon_t\Big|\\
--   &\le\frac1N\sum_{i=1}^m\sqrt{N\hat\mu_i}=\frac1{\sqrt N}\sum_{i=1}^m\sqrt{\hat\mu_i}\le\sqrt{\frac mN}.
--   \end{aligned}$$
--
--   The statement is deterministic: it holds for every sample. The bound $\widehat{\mathfrak R}_N\le\sqrt{m/N}$ is the complexity estimate behind the first term $8\sqrt{(\tau+m)/N}$ of Theorem 4.
--
--   **Formalization Note** The $\ell_1$ norm in the first equality is written out coordinatewise: the $i$-th coordinate of $\frac1N\sum_t\epsilon_tI_t$ is $\frac1N\sum_t\epsilon_t\mathbb I[i_t=i]$. The paper's chain has two further intermediate lines, a reindexing over the $N\hat\mu_i$ draws of type $i$ and an exact binomial expression whose coefficient is misprinted ($\binom{m}{\lceil N\hat\mu_i/2\rceil}$ for $\binom{N\hat\mu_i}{\lceil N\hat\mu_i/2\rceil}$); they are omitted, and the inequality $\le\frac1N\sum_i\sqrt{N\hat\mu_i}$ is stated directly from the preceding line. Signs are booleans ($\text{true}\mapsto+1$). Types are 0-based.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 4, p. 44, displays after "where ℜ̂_N is the empirical Rademacher complexity" and "By linearity and duality of norms, we have"

import Mathlib
import Definitions.Def_DynAssortPers_TypeDist_IIDSampling
import Definitions.Def_DynAssortPers_TypeDist_Estimator

namespace DynAssortPers.TypeDist

open Finset

theorem display_p44_rademacher {m N : ℕ} (hN : 0 < N) (x : Fin N → Fin m) :
    radHat x = (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        ∑ i : Fin m, |(1 / N : ℝ) * ∑ t, sgn (ε t) * (if x t = i then 1 else 0)| ∧
    (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        ∑ i : Fin m, |(1 / N : ℝ) * ∑ t, sgn (ε t) * (if x t = i then 1 else 0)|
      = (1 / N : ℝ) * ∑ i : Fin m, (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        |∑ t, (if x t = i then 1 else 0) * sgn (ε t)| ∧
    (1 / N : ℝ) * ∑ i : Fin m, (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        |∑ t, (if x t = i then 1 else 0) * sgn (ε t)|
      ≤ (1 / N : ℝ) * ∑ i : Fin m, Real.sqrt (N * muHat x i) ∧
    (1 / N : ℝ) * ∑ i : Fin m, Real.sqrt (N * muHat x i)
      = (1 / Real.sqrt N) * ∑ i : Fin m, Real.sqrt (muHat x i) ∧
    (1 / Real.sqrt N) * ∑ i : Fin m, Real.sqrt (muHat x i) ≤ Real.sqrt (m / N) := by sorry

end DynAssortPers.TypeDist
