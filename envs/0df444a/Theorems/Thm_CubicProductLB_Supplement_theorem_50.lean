-- Prove2me | Theorems.Thm_CubicProductLB_Supplement_theorem_50
-- name    : CubicProductLB.Supplement.theorem_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:43:55.799292+00:00
-- url     : https://prove2.me/theorems/55592018-616b-428a-b0f1-81037e647dcc
-- title:
--   Theorem 50 — all higher fixed degrees over $\mathbb F_p$: $L^{(p,q)}_d(n) = \Omega(n^{d/(d-3)}/(\log(2+n))^{3/(d-3)})$
-- statement:
--   Fix a prime $p>3$ and an odd integer $q>1$ with $\gcd(p,q)=1$. Let $L^{(p,q)}_d(n)$ be the minimum total variable-occurrence cost of an exact representation
--   $$F_{q,n}(x) = \prod_j P_j(x) \qquad (x \in \{-1,1\}^n),\qquad P_j \in \mathbb F_p[x_1,\dots,x_n],\ \deg P_j \le d,$$
--   with $+\infty$ if none exists. Then:
--
--   1. $$L^{(p,q)}_4(n) = \Omega_{p,q}\!\left(\frac{n^4}{(\log(2+n))^3}\right);$$
--   2. for every fixed integer $d \ge 4$, $$L^{(p,q)}_d(n) = \Omega_{p,q,d}\!\left(\frac{n^{d/(d-3)}}{(\log(2+n))^{3/(d-3)}}\right);$$
--   3. in particular, every fixed degree $d>4$ has a superlinear polynomial occurrence lower bound over $\mathbb F_p$: $L^{(p,q)}_d(n) \ge c\,n^{1+\varepsilon}$ for some $\varepsilon>0$, $c>0$ and all large $n$.
--
--   Each $\Omega$ means: there are $c>0$ and $n_0$, depending on the subscripted parameters, with $L \ge c\cdot\text{bound}$ for all $n \ge n_0$.
--
--   **Formalization Note** $L^{(p,q)}_d$ is `minCostP d p q`, compared through `ENNReal.ofReal`. Factors are listed factors (repeated terms and arbitrary powers allowed) whose function has multilinear degree at most $d$ on the cube. Exponents are real; $\log$ is natural.
--
--   Differences from the source:
--   - generalization: Pⱼ ∈ F_p[x₁,…,xₙ] with deg Pⱼ ≤ d, cost of its monomials → listed factors (repeats, arbitrary powers) whose function has multilinear degree ≤ d on {−1,1}ⁿ; reason: the paper's degree convention (Definition 1, p.3; "as above", p.65); every formal degree-≤ d polynomial is such a listing at the same cost, so the Lean minimum is at most the formal one and its lower bound implies the printed one
--   - encoding: Ω_{p,q}(·), Ω_{p,q,d}(·) and "a superlinear polynomial occurrence lower bound" → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, ofReal (c · bound) ≤ L; for d > 4, ∃ ε > 0 with bound n^{1+ε}; reason: the standard meanings; +∞ on an empty class satisfies every bound
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 50, Eqs. (421)–(423), p.65

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_minCostP

namespace CubicProductLB.Supplement

/-- Theorem 50 (All higher fixed degrees over `F_p`) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 50, Eqs. (422)–(423), p.65). Fix a prime
`p > 3` and an odd integer `q > 1` with `gcd(p, q) = 1`. Then
`L^{(p,q)}_4(n) = Ω_{p,q}(n⁴ / (log(2 + n))³)`; more generally, for every fixed integer `d ≥ 4`,
`L^{(p,q)}_d(n) = Ω_{p,q,d}(n^{d/(d−3)} / (log(2 + n))^{3/(d−3)})`. In particular, every fixed degree
`d > 4` has a superlinear polynomial occurrence lower bound over `F_p`.

**Formalization Note** `L^{(p,q)}_d` is `minCostP d p q` in `ℕ∞` (`⊤` on an empty class), compared in
`ℝ≥0∞` via `ENNReal.ofReal`. Each `Ω` is read as `∃ c > 0, ∃ n₀, ∀ n ≥ n₀`, with constants chosen after
the subscripted parameters and before `n`. "Superlinear polynomial lower bound" is read as
`L ≥ c n^{1+ε}` for some `ε > 0` and all large `n`. Exponents are real; `log` is natural. -/
theorem theorem_50 (p q : ℕ) (hp : p.Prime) (h3 : 3 < p) (hq : Odd q) (hq1 : 1 < q)
    (hpq : Nat.Coprime p q) :
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ENNReal.ofReal (c * (n : ℝ) ^ 4 / Real.log (2 + n) ^ 3) ≤ ((minCostP 4 p q n : ℕ∞) : ENNReal)) ∧
    (∀ d : ℕ, 4 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ENNReal.ofReal (c * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) - 3)) /
        Real.log (2 + n) ^ ((3 : ℝ) / ((d : ℝ) - 3))) ≤ ((minCostP d p q n : ℕ∞) : ENNReal)) ∧
    (∀ d : ℕ, 4 < d → ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ENNReal.ofReal (c * (n : ℝ) ^ (1 + ε)) ≤ ((minCostP d p q n : ℕ∞) : ENNReal)) := by sorry

end CubicProductLB.Supplement
