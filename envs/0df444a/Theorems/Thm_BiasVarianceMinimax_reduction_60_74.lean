-- Prove2me | Theorems.Thm_BiasVarianceMinimax_reduction_60_74
-- name    : BiasVarianceMinimax.reduction_60_74
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:17.04372+00:00
-- url     : https://prove2.me/theorems/34007356-2e6d-4385-8069-b7cda90328a7
-- title:
--   (60)–(69), (74) — reduction of (60) to the one-variable problem
-- statement:
--   Let $n\ge 2$ and let $a$ be an optimal solution of (24), which is problem (74). Then the value of (24) at $a$ is the least $S$ for which some $(w,\eta)$ is feasible for
--
--   $$\min_{w,\eta}S\quad\text{subject to}\quad S=\Big(\eta^{q_1}\sum_j\frac{w_j}{(j+n_0)^{\alpha q_1}}\Big)^2=\frac1{\eta^{2q_2}}\sum_j (j+n_0)^{2\alpha q_2}w_j^2,\quad\eta\le K,\quad\sum_j w_j=1,$$
--
--   and it is attained at $(w^*(a),\eta^*)$.
--
--   Problem (60) balances the scaled bias and variance terms under the budget $\eta\le K$; this statement says (24) computes it.
--
--   Differences from the source:
--   - generalization: Appendix C assumes n₀ = 0 → the statement holds for every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
--   - reading: η in (60) without a sign → η > 0; reason: p.51 has g(d) = ηd for some η > 0
--   - encoding: no bound on n → n ≥ 2; reason: the matrix in Ξ is singular at n = 1, so only an undefined case is excluded
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (60), p.51; (61)–(69), p.52; p.53; (74), p.54

import Mathlib
import Definitions.Def_BiasVarianceMinimax_IsOptimal
import Definitions.Def_BiasVarianceMinimax_weightStar

namespace BiasVarianceMinimax

/-- **Reduction of (60) to the one-variable problem (74).** Lam, Zhang & Zhang, arXiv:1902.04673v1,
(60), p.51; (61)–(69), p.52; p.53; (74), p.54.

For `n ≥ 2` and an optimal solution `a` of (24), which is (74): the value of (24) at `a` is the least
`S` over the feasible triples of (60), and it is attained at `(w∗(a), η∗)`.

**Formalization Note.** Appendix C sets `n₀ = 0`; this statement keeps `n₀`. `η > 0` is taken from
p.51 ("`g(d) = ηd` for some `η > 0`"). -/
theorem reduction_60_74 (q₁ q₂ K : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hK : 0 < K) (n₀ n : ℕ)
    (hn : 2 ≤ n) (a : ℝ) (ha : IsOptimal q₁ q₂ K n₀ n a) :
    IsLeast {S : ℝ | ∃ (w : Fin n → ℝ) (η : ℝ), Feasible60 q₁ q₂ K n₀ n w η S}
      (objective24 q₁ q₂ n₀ n a) ∧
    Feasible60 q₁ q₂ K n₀ n (twoDecay q₁ q₂ n₀ n a) (etaStar q₁ q₂ n₀ n a)
      (objective24 q₁ q₂ n₀ n a) := by sorry

end BiasVarianceMinimax
