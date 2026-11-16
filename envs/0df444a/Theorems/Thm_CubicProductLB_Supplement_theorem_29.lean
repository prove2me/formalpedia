-- Prove2me | Theorems.Thm_CubicProductLB_Supplement_theorem_29
-- name    : CubicProductLB.Supplement.theorem_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:42:36.636061+00:00
-- url     : https://prove2.me/theorems/171d7c79-cabc-4417-bc72-7b481822c618
-- title:
--   Theorem 29 — closed-form lifting: $L_d(n) \ge c_d\,n^{a_d}/(\log(2+n))^{b_d}$ with $a_d = ad/(d_0+a(d-d_0))$
-- statement:
--   Work over $\mathbb F_3$ with a fixed prime target modulus $p>3$, and let $L_d(n)$ be the minimum occurrence cost of a representation of $F_{p,n}$ as a product of factors of degree at most $d$ ($+\infty$ if there is none).
--
--   Fix integers $d_0 \ge 1$ and $d \ge d_0$ and real constants $c>0$, $0 < a \le d_0+1$, $b \ge 0$. Suppose that for all sufficiently large $n$,
--   $$L_{d_0}(n) \ge c\,\frac{n^a}{(\log(2+n))^b}.$$
--   Then there is a constant $c_d>0$ such that
--   $$L_d(n) \ge c_d\,\frac{n^{a_d}}{(\log(2+n))^{b_d}},\qquad a_d = \frac{ad}{d_0+a(d-d_0)},\quad b_d = \frac{d_0 b}{d_0+a(d-d_0)}.$$
--   The constant $c_d$ may depend on $p, d_0, d, a, b, c$, but not on $n$. This is the closed form of iterating Theorem 28 from degree $d_0$ to degree $d$.
--
--   **Formalization Note** $L_d$ is the published `minCost d p`, compared through `ENNReal.ofReal`. The hypothesis is eventual and the conclusion is stated for every $n$, as printed. Powers are real powers; $d-d_0$ is a real difference.
--
--   Differences from the source:
--   - reading: deg Pⱼ ≤ d in (369), with L_d the minimum occurrence cost → the published CubicProductLB.minCost: listed factors whose function has multilinear degree ≤ d on X_n, cost the listed occurrence cost, ⊤ on an empty class; reason: the paper's degree convention (Definition 1, p.3); p.43 replaces every factor by its multilinear representative without increasing degree or cost; reused as published
--   - encoding: real lower bounds on L_d(n) ∈ ℕ ∪ {+∞} → ENNReal.ofReal (bound) ≤ (minCost … : ℝ≥0∞); reason: an empty class gives +∞, which satisfies every bound, as on p.42; same instances
--   - reading: Ld₀(n) ≥ c n^a/(log(2+n))^b with a constant c → hypothesis 0 < c; reason: the page treats c as a positive constant; with c ≤ 0 the hypothesis says nothing
--   - reading: (390) printed with no range of n → the conclusion for every n : ℕ; reason: the literal, stronger reading; equivalent to "for all large n" because L_d(n) ≥ 1 for n ≥ 1 and the bound is 0 at n = 0
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 29, Eqs. (389)–(390), p.48

import Mathlib
import Definitions.Def_CubicProductLB_minCost

namespace CubicProductLB.Supplement

/-- Theorem 29 (Closed-form lifting from an arbitrary base degree) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 29, Eqs. (389)–(390),
p.48). Fix a prime target modulus `p > 3` over `F_3` and integers `d₀ ≥ 1`, `d ≥ d₀`. Suppose that for all
sufficiently large `n`, `L_{d₀}(n) ≥ c n^a / (log(2 + n))^b` with `c > 0`, `0 < a ≤ d₀ + 1`, `b ≥ 0`.
Then there is `c_d > 0` with `L_d(n) ≥ c_d n^{a_d} / (log(2 + n))^{b_d}`, where
`a_d = a d / (d₀ + a(d − d₀))` and `b_d = d₀ b / (d₀ + a(d − d₀))`.

**Formalization Note** `L_d` is the base mission's `minCost d p` (`⊤` on an empty class), compared in
`ℝ≥0∞` via `ENNReal.ofReal`. The hypothesis is eventual; the conclusion has no threshold on `n`, as
printed, so it is stated for every `n`. `c_d` may depend on `p, d₀, d, a, b, c`. Powers are real
powers; `d − d₀` is real subtraction (here `d ≥ d₀`). -/
theorem theorem_29 (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (d₀ d : ℕ) (hd₀ : 1 ≤ d₀) (hd : d₀ ≤ d)
    (a b c : ℝ) (hc : 0 < c) (ha : 0 < a) (had : a ≤ (d₀ : ℝ) + 1) (hb : 0 ≤ b)
    (hL : ∃ N : ℕ, ∀ n ≥ N,
      ENNReal.ofReal (c * (n : ℝ) ^ a / Real.log (2 + n) ^ b) ≤ ((minCost d₀ p n : ℕ∞) : ENNReal)) :
    ∃ c_d : ℝ, 0 < c_d ∧ ∀ n : ℕ,
      ENNReal.ofReal (c_d * (n : ℝ) ^ (a * d / ((d₀ : ℝ) + a * ((d : ℝ) - d₀))) /
        Real.log (2 + n) ^ ((d₀ : ℝ) * b / ((d₀ : ℝ) + a * ((d : ℝ) - d₀)))) ≤
        ((minCost d p n : ℕ∞) : ENNReal) := by sorry

end CubicProductLB.Supplement
