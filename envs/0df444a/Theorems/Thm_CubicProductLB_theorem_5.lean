-- Prove2me | Theorems.Thm_CubicProductLB_theorem_5
-- name    : CubicProductLB.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:26.698731+00:00
-- url     : https://prove2.me/theorems/d9b88720-3347-4ee2-aba8-e422c52e3116
-- title:
--   Theorem 5 — cubic representations of $F_{p,n}$ over $\mathbb F_3$ satisfy $\gamma^n \le C^2$
-- statement:
--   Fix a prime target modulus $p > 3$. There exist constants $\gamma > 1$ and $n_1$ such that every cubic representation of $F_{p,n}$ of original occurrence cost $C$, for $n \ge n_1$, satisfies
--   $$\gamma^n \le C^2.$$
--   In particular $L_3(n) = 2^{\Omega_p(n)}$: there are $c > 0$ and $n_0$, depending on $p$, with $L_3(n) \ge 2^{cn}$ for all $n \ge n_0$.
--
--   The representations are products over $\mathbb F_3$ of any number of factors, each of multilinear degree at most three on the sign cube, required to agree with the target only on $X_n$; the cost counts variable occurrences in the original listings. This is the main quantitative result of the paper. For $p = 2$ and $p = 3$ the target has representations of polynomial cost, so the hypothesis $p > 3$ is essential.
--
--   **Formalization Note** $L_3(n)$ takes values in $\mathbb N \cup \{\infty\}$, and the inequality is stated in the extended nonnegative reals, so that the value $+\infty$ on an empty class satisfies it.
--
--   Differences from the source:
--   - reading: L₃(n) = 2^{Ω_p(n)} → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, 2^{cn} ≤ L₃(n); reason: this is the standard meaning of the asymptotic lower bound, with c, n₀ depending on p
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 5, p.4

import Mathlib
import Definitions.Def_CubicProductLB_ProductRep
import Definitions.Def_CubicProductLB_CubicRep
import Definitions.Def_CubicProductLB_minCost

namespace CubicProductLB

/-- Theorem 5 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 5, p.4). Fix a prime target modulus `p > 3`. There exist constants `γ > 1` and
`n₁` such that every cubic representation of `F_{p,n}` of original occurrence cost `C`, for `n ≥ n₁`,
satisfies `γ^n ≤ C²`. In particular `L₃(n) = 2^{Ω_p(n)}`.

**Formalization Note** The constants come after `p` and before `n`, as printed. `L₃(n) = 2^{Ω_p(n)}` is
read as: there are `c > 0` and `n₀`, depending on `p`, with `L₃(n) ≥ 2^{cn}` for `n ≥ n₀`. `L₃` is compared in
`ℝ≥0∞` through the coercion from `ℕ∞`, so `+∞` on an empty class stays `+∞`. -/
theorem theorem_5 (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    (∃ γ : ℝ, 1 < γ ∧ ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ r : CubicRep p n, γ ^ n ≤ (r.cost : ℝ) ^ 2) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ENNReal.ofReal ((2 : ℝ) ^ (c * (n : ℝ))) ≤ ((minCost 3 p n : ℕ∞) : ENNReal)) := by sorry

end CubicProductLB
