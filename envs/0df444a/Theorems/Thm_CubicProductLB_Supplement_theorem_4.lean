-- Prove2me | Theorems.Thm_CubicProductLB_Supplement_theorem_4
-- name    : CubicProductLB.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:40:25.039126+00:00
-- url     : https://prove2.me/theorems/237753a0-5c58-467a-a249-cfab0f2634f2
-- title:
--   Theorem 4 — reconstruction form: $c^n \le (Kn^2C)^2$ and $C \ge n^a$ for cubic representations of $F_{p,n}$
-- statement:
--   Fix a prime target modulus $p>3$ in the characteristic-three model: the coefficient field is $\mathbb F_3$, and $F_{p,n}(x) = -1$ if $p$ divides the number $w(x)$ of negative coordinates of $x \in \{-1,1\}^n$, and $1$ otherwise. A cubic representation is a finite product of listed factors over $\mathbb F_3$, each of multilinear degree at most three on $\{-1,1\}^n$, agreeing with $F_{p,n}$ on the sign cube; its occurrence cost $C$ is the total number of variable occurrences in the listed monomials.
--
--   There exist constants $c>1$, $K \ge 1$ and $n_0$ such that every cubic representation of $F_{p,n}$ of occurrence cost $C$, for $n \ge n_0$, satisfies
--   $$c^n \le (K n^2 C)^2.$$
--   Consequently, for every real $a>0$ there is $N(a)$ such that $C \ge n^a$ whenever $n \ge N(a)$.
--
--   Both clauses are part of the statement. The theorem is the paper's reconstruction-route lower bound, retained beside the direct bound $\gamma^n \le C^2$ of Theorem 5 because it exposes a different structural route.
--
--   **Formalization Note** The cubic representations and their cost are the base mission's published `CubicRep` and `ProductRep.cost`. The constants are chosen after $p$ and before $n$; $N$ is chosen after $a$. $n^a$ is a real power.
--
--   Differences from the source: none.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 4, p.4

import Mathlib
import Definitions.Def_CubicProductLB_ProductRep
import Definitions.Def_CubicProductLB_CubicRep

namespace CubicProductLB.Supplement

/-- Theorem 4 (Reconstruction form) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 4, p.4). Fix a prime target modulus `p > 3` in the
characteristic-three model. There exist constants `c > 1`, `K ≥ 1` and `n₀` such that every cubic
representation of `F_{p,n}` of occurrence cost `C`, for `n ≥ n₀`, satisfies `c^n ≤ (K n² C)²`.
Consequently, for every real `a > 0` there is `N(a)` such that `C ≥ n^a` whenever `n ≥ N(a)`.

**Formalization Note** The cost is the published listed occurrence cost `ProductRep.cost` of the base
mission. The constants are chosen after `p` and before `n` and the representation, as printed;
`N` is chosen after `a`. `n^a` is a real power. -/
theorem theorem_4 (p : ℕ) (hp : p.Prime) (h3 : 3 < p) :
    (∃ c : ℝ, 1 < c ∧ ∃ K : ℝ, 1 ≤ K ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ r : CubicRep p n,
      c ^ n ≤ (K * (n : ℝ) ^ 2 * (r.cost : ℝ)) ^ 2) ∧
    (∀ a : ℝ, 0 < a → ∃ N : ℕ, ∀ n ≥ N, ∀ r : CubicRep p n, (n : ℝ) ^ a ≤ (r.cost : ℝ)) := by sorry

end CubicProductLB.Supplement
