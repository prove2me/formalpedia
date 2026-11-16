-- Prove2me | Theorems.Thm_CubicProductLB_Supplement_theorem_28
-- name    : CubicProductLB.Supplement.theorem_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:42:16.704771+00:00
-- url     : https://prove2.me/theorems/4a7c7b5d-5d61-4ac7-a7a2-ba274e8d9f4f
-- title:
--   Theorem 28 — lifting $L_d(n) \ge c\,n^a/(\log(2+n))^b$ to degree $d+1$
-- statement:
--   Work over $\mathbb F_3$ with a fixed prime target modulus $p>3$, and let $L_d(n)$ be the minimum occurrence cost of a representation of $F_{p,n}$ as a product of factors of degree at most $d$ ($+\infty$ if there is none).
--
--   Fix $d \ge 1$ and real constants $c>0$, $0 < a \le d+1$, $b \ge 0$. Suppose that for all sufficiently large $n$,
--   $$L_d(n) \ge c\,\frac{n^a}{(\log(2+n))^b}.$$
--   Then there is a constant $c'>0$ such that
--   $$L_{d+1}(n) \ge c'\,\frac{n^{(d+1)a/(d+a)}}{(\log(2+n))^{db/(d+a)}}.$$
--   All constants may depend on $d, p, a, b$ (and $c$). Iterated, this converts one polynomial lower bound into lower bounds at every higher fixed degree.
--
--   **Formalization Note** $L_d$ is the published `minCost d p`, compared in $[0,\infty]$ through `ENNReal.ofReal`. The hypothesis is eventual; the conclusion is stated for every $n$, since the page prints no threshold. Powers are real powers; $\log$ is natural.
--
--   Differences from the source:
--   - reading: deg Pⱼ ≤ d in (369), with L_d the minimum occurrence cost → the published CubicProductLB.minCost: listed factors whose function has multilinear degree ≤ d on X_n, cost the listed occurrence cost, ⊤ on an empty class; reason: the paper's degree convention (Definition 1, p.3); p.43 replaces every factor by its multilinear representative without increasing degree or cost; reused as published
--   - encoding: real lower bounds on L_d(n) ∈ ℕ ∪ {+∞} → ENNReal.ofReal (bound) ≤ (minCost … : ℝ≥0∞); reason: an empty class gives +∞, which satisfies every bound, as on p.42; same instances
--   - reading: Ld(n) ≥ c n^a/(log(2+n))^b with a constant c → hypothesis 0 < c; reason: the page treats c as a positive constant (its proof divides by it and produces c′ > 0); with c ≤ 0 the hypothesis says nothing
--   - reading: (383) printed with no range of n → the conclusion for every n : ℕ; reason: the literal, stronger reading; it is equivalent to "for all large n" because L_{d+1}(n) ≥ 1 for n ≥ 1 (F_{p,n} is nonconstant, so some factor has positive cost) and the bound is 0 at n = 0
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 28, Eqs. (382)–(383), p.46

import Mathlib
import Definitions.Def_CubicProductLB_minCost

namespace CubicProductLB.Supplement

/-- Theorem 28 (Lifting a polynomial occurrence bound) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 28, Eqs. (382)–(383), p.46). Fix
`d ≥ 1` and a prime target modulus `p > 3` over `F_3`. Suppose that for all sufficiently large `n`,
`L_d(n) ≥ c n^a / (log(2 + n))^b` with `c > 0`, `0 < a ≤ d + 1`, `b ≥ 0`. Then there is `c' > 0` with
`L_{d+1}(n) ≥ c' n^{(d+1)a/(d+a)} / (log(2 + n))^{db/(d+a)}`.

**Formalization Note** `L_d` is the base mission's `minCost d p` (`⊤` on an empty class), compared in
`ℝ≥0∞` via `ENNReal.ofReal`. The hypothesis is eventual, as printed. The conclusion carries no
threshold on `n`, as printed (Eq. (383)), so it is stated for every `n`. `c'` may depend on
`d, p, a, b, c`. Powers are real powers, `log` is the natural logarithm. -/
theorem theorem_28 (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : p.Prime) (h3 : 3 < p)
    (a b c : ℝ) (hc : 0 < c) (ha : 0 < a) (had : a ≤ (d : ℝ) + 1) (hb : 0 ≤ b)
    (hL : ∃ N : ℕ, ∀ n ≥ N,
      ENNReal.ofReal (c * (n : ℝ) ^ a / Real.log (2 + n) ^ b) ≤ ((minCost d p n : ℕ∞) : ENNReal)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ,
      ENNReal.ofReal (c' * (n : ℝ) ^ (((d : ℝ) + 1) * a / ((d : ℝ) + a)) /
        Real.log (2 + n) ^ ((d : ℝ) * b / ((d : ℝ) + a))) ≤ ((minCost (d + 1) p n : ℕ∞) : ENNReal) := by sorry

end CubicProductLB.Supplement
