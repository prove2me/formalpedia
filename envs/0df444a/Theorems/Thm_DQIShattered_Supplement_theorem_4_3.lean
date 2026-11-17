-- Prove2me | Theorems.Thm_DQIShattered_Supplement_theorem_4_3
-- name    : DQIShattered.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:35:21.699639+00:00
-- url     : https://prove2.me/theorems/6dbdd5ad-e52d-415c-8aad-a9a84517f5df
-- title:
--   Theorem 4.3 — Failure of stable algorithms
-- statement:
--   There is an $\varepsilon_0>0$ such that, for every $\varepsilon\in(0,\varepsilon_0)$, some $k_0(\varepsilon)\ge3$ has the following property. For every $k\ge k_0(\varepsilon)$, real $D\ge k$, and $\beta$ satisfying
--   $$
--   (1+\varepsilon)\sqrt{\frac{2\ln k}{D}}\le\beta\le\sqrt{\frac{k}{2D}},
--   $$
--   there exists $\iota_*=\iota_*(k,D,\beta,\varepsilon)>0$, independent of $N$. If $(A_N)$ is a family of probability-law-valued samplers that is $\iota$-stable under replacement of one independently sampled clause for a fixed $\iota\in(0,\iota_*]$, then
--   $$
--   \liminf_{N\to\infty}\mathbb E_{H\sim\mathbb G_{\mathrm{ER}}(N,k,D)}
--   W_1(\mu_{\beta,H},A_N(H))>0.
--   $$
--
--   Differences from the source:
--   - reading: $\varepsilon>0$ is sufficiently small → Lean states $\exists\varepsilon_0>0$ and quantifies every $0<\varepsilon<\varepsilon_0$; reason: this is the standard uniform meaning of “sufficiently small”
--   - encoding: $A_N$ is $\iota$-stable for an $\iota$ independent of $N$ → Lean represents $(A_N)$ as one dependent sampler family and places the fixed $\iota$ before the universal quantifier over $N$; reason: this preserves the source's quantifier order
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 4.3, p.18, eq. (4.4)

import Mathlib
import Definitions.Def_DQIShattered_Supplement_Framework

namespace DQIShattered

namespace Supplement

/-- **Theorem 4.3 (Failure of stable algorithms).**
Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…,
p.18.

There is a positive meaning of 'sufficiently small' such that, for every eligible `ε`, all
sufficiently large `k`, every `D ≥ k`, and every `β` in (4.4), there is a constant
`ι_* = ι_*(k,D,β,ε) > 0`, independent of `N`. Any distribution-valued sampler family which is
`ι`-stable for one fixed `ι ∈ (0,ι_*]` has strictly positive asymptotic lower normalized-
Wasserstein error from the Gibbs measure. -/
theorem theorem_4_3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ D : ℝ, (k : ℝ) ≤ D → ∀ β : ℝ, InHardRange k D ε β →
          StableObstruction k D β := by sorry

end Supplement

end DQIShattered
