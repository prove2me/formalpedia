-- Prove2me | Theorems.Thm_CubicProductLB_Supplement_theorem_32
-- name    : CubicProductLB.Supplement.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:43:12.773434+00:00
-- url     : https://prove2.me/theorems/12e92985-0306-40a6-b4a3-587c809811cb
-- title:
--   Theorem 32 — cubic product representations of $F_{q,n}$ over $\mathbb F_p$ need $m \ge 2^{c_{p,q}n}$ factors
-- statement:
--   Fix a prime $p>3$ and an odd integer $q>1$ with $\gcd(p,q)=1$. Over $\mathbb F_p$, let $F_{q,n}(x) = -1$ if $q$ divides the number of negative coordinates of $x \in \{-1,1\}^n$, and $1$ otherwise. A cubic product representation is an identity
--   $$F_{q,n}(x) = \prod_{j=1}^m P_j(x) \qquad \text{for all } x \in \{-1,1\}^n,$$
--   with $P_j \in \mathbb F_p[x_1,\dots,x_n]$ and $\deg P_j \le 3$ (functional equality on the sign cube).
--
--   There exist constants $c_{p,q}>0$ and $n_0(p,q)$ such that for every $n \ge n_0(p,q)$, every cubic product representation satisfies
--   $$m \ge 2^{c_{p,q} n}.$$
--   Consequently, any syntactic size measure charging at least one unit for every nonconstant listed factor is also $2^{\Omega_{p,q}(n)}$.
--
--   This extends the exponential cubic lower bound from $\mathbb F_3$ to every prime field of characteristic greater than three, for every odd target modulus coprime to the characteristic.
--
--   **Formalization Note** $m$ counts every factor, constants included. The second sentence is stated, with its own constants $c>0$ and $n_0$, for the number of factors that are nonconstant as functions on $\{-1,1\}^n$.
--
--   Differences from the source:
--   - generalization: any syntactic size measure charging at least one unit per nonconstant listed factor is 2^{Ω_{p,q}(n)} → the number of factors nonconstant as functions on {−1,1}ⁿ is ≥ 2^{cn} for n ≥ n₀; reason: a factor nonconstant on the cube is nonconstant as a listing, so every such measure is at least this count and the Lean clause implies the printed one
--   - encoding: 2^{Ω_{p,q}(n)} → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, count ≥ 2^{c n}; reason: the standard meaning, as in the published goal
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 32, Definition 31, Eqs. (397)–(398), p.51

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_PolyCubicRep

namespace CubicProductLB.Supplement

/-- Theorem 32 (General prime-field cubic lower bound) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 32, p.51). Fix a prime `p > 3` and an
odd integer `q > 1` with `gcd(p, q) = 1`. There exist `c_{p,q} > 0` and `n₀(p, q)` such that for every
`n ≥ n₀(p, q)`, every cubic product representation (398) of `F_{q,n}` over `F_p` has `m ≥ 2^{c_{p,q} n}`
factors. Consequently any syntactic size measure charging at least one unit for every nonconstant
listed factor is also `2^{Ω_{p,q}(n)}`.

**Formalization Note** `m` is `factors.length` (constant factors included). The second sentence is
stated for the number of factors that are nonconstant as functions on `{-1, 1}^n`, with its own
constants; that number is at most the number of syntactically nonconstant listed factors, hence at
most any such size measure, so this clause implies the printed one. `2^{Ω_{p,q}(n)}` is read as
`∃ c > 0, ∃ n₀, ∀ n ≥ n₀, · ≥ 2^{cn}`, constants depending on `p, q` only. -/
theorem theorem_32 (p q : ℕ) (hp : p.Prime) (h3 : 3 < p) (hq : Odd q) (hq1 : 1 < q)
    (hpq : Nat.Coprime p q) :
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ r : PolyCubicRep p q n,
      (2 : ℝ) ^ (c * (n : ℝ)) ≤ (r.factors.length : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ r : PolyCubicRep p q n,
      (2 : ℝ) ^ (c * (n : ℝ)) ≤ (r.nonconstCount : ℝ)) := by sorry

end CubicProductLB.Supplement
