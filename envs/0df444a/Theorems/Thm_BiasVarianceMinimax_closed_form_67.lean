-- Prove2me | Theorems.Thm_BiasVarianceMinimax_closed_form_67
-- name    : BiasVarianceMinimax.closed_form_67
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:53.63466+00:00
-- url     : https://prove2.me/theorems/4454b93b-0fee-4eb6-b00e-bfc4002d21f9
-- title:
--   (67), (70)–(73) — closed form of the minimum-norm problem
-- statement:
--   Let $n\ge 2$, $a\in\mathbb R$, and let $w^*(a)$ be the two-decay vector with $(\lambda_1,\lambda_2)^\top=\Xi(a,1)^\top$. Then $w^*(a)$ solves
--
--   $$\min_w\ \|\Sigma^{1/2}w\|\quad\text{subject to}\quad \mu'w=a,\quad \mathbb 1'w=1,$$
--
--   with $\Sigma=\mathrm{diag}((j+n_0)^{2\alpha q_2})$ and $\mu=((j+n_0)^{-\alpha q_1})_j$, and $\|\Sigma^{1/2}w^*(a)\|^2=\xi_{11}a^2+2\xi_{12}a+\xi_{22}$.
--
--   This reduces the $n$-dimensional weight choice to the choice of the one scalar $a$, and it is the source of the two decay rates.
--
--   Differences from the source:
--   - generalization: Appendix C assumes n₀ = 0 → the statement holds for every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
--   - encoding: no bound on n → n ≥ 2; reason: the matrix in Ξ is singular at n = 1, so only an undefined case is excluded
--   - encoding: min of the norm → minimality of the squared norm; reason: the same minimizers
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (67), p.52; (70)–(72), p.53; (73), p.54

import Mathlib
import Definitions.Def_BiasVarianceMinimax_IsOptimal
import Definitions.Def_BiasVarianceMinimax_weightStar

namespace BiasVarianceMinimax

/-- **Closed form of problem (67).** Lam, Zhang & Zhang, arXiv:1902.04673v1, (67), p.52; (70)–(72),
p.53; the display after (72) and (73), p.54.

For `n ≥ 2` and every `a`, the two-decay vector `w∗(a)` is feasible for
`min ‖Σ^(1/2) w‖` subject to `μ′w = a`, `𝟙′w = 1`, minimizes it, and its squared value is
`ξ₁₁ a² + 2 ξ₁₂ a + ξ₂₂`.

**Formalization Note.** Appendix C sets `n₀ = 0`; this statement keeps `n₀`. The exponents of (70),
`α(q₁ + 2q₂)` and `2αq₂`, are the `κ₁`, `κ₂` of Theorem 8. Minimality is stated for the squared norm.
`n ≥ 2` makes `Ξ` a genuine inverse. -/
theorem closed_form_67 (q₁ q₂ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (n₀ n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    muSum q₁ q₂ n₀ n (twoDecay q₁ q₂ n₀ n a) = a ∧
    ∑ j, twoDecay q₁ q₂ n₀ n a j = 1 ∧
    (∀ v : Fin n → ℝ, muSum q₁ q₂ n₀ n v = a → ∑ j, v j = 1 →
      sigmaSum q₁ q₂ n₀ n (twoDecay q₁ q₂ n₀ n a) ≤ sigmaSum q₁ q₂ n₀ n v) ∧
    sigmaSum q₁ q₂ n₀ n (twoDecay q₁ q₂ n₀ n a) = quadForm q₁ q₂ n₀ n a := by sorry

end BiasVarianceMinimax
