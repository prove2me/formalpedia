-- Prove2me | Theorems.Thm_CubicProductLB_Supplement_theorem_25
-- name    : CubicProductLB.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:41:31.61324+00:00
-- url     : https://prove2.me/theorems/9c67a4e4-f2b4-47d7-8549-340a06c30fb5
-- title:
--   Theorem 25 — general degree-lifting inequality $S \ge f(\max\{1,\lfloor c_d\min\{n, n^{(d+1)/d}/(S+1)^{1/d}\}\rfloor\})$
-- statement:
--   Work over $\mathbb F_3$ with a fixed prime target modulus $p>3$, and let $L_d(n)$ be the minimum occurrence cost of a representation of $F_{p,n}$ on $\{-1,1\}^n$ as a product of factors of degree at most $d$ ($+\infty$ if there is none).
--
--   Fix $d \ge 1$. Let $f : \mathbb N \to [0,\infty)$ be nondecreasing with $L_d(k) \ge f(k)$ for every $k \ge 1$. There is a constant $c_d>0$ such that for every $n \ge 1$ and every degree-at-most-$(d+1)$ representation of $F_{p,n}$ of occurrence cost $S$,
--   $$S \ge f\!\left(\max\left\{1, \left\lfloor c_d \min\left\{n, \frac{n^{(d+1)/d}}{(S+1)^{1/d}}\right\}\right\rfloor\right\}\right).$$
--
--   Thus the least $S$ satisfying the inequality is an implicit lower bound for $L_{d+1}(n)$; no continuity or regularity of $f$ is required. The inequality turns any lower bound at degree $d$ into one at degree $d+1$.
--
--   **Formalization Note** $L_d$ is the published `minCost d p`, compared with $f$ through `ENNReal.ofReal`. $c_d$ is chosen after $d$, $p$ and $f$, as printed. Powers are real powers and $\lfloor\cdot\rfloor$ is the natural-number floor.
--
--   Differences from the source:
--   - reading: deg Pⱼ ≤ d in (369), with L_d the minimum occurrence cost → the published CubicProductLB.minCost: listed factors whose function has multilinear degree ≤ d on X_n, cost the listed occurrence cost, ⊤ on an empty class; reason: the paper's degree convention (Definition 1, p.3); p.43 replaces every factor by its multilinear representative without increasing degree or cost; reused as published
--   - encoding: real lower bounds on L_d(n) ∈ ℕ ∪ {+∞} → ENNReal.ofReal (bound) ≤ (minCost … : ℝ≥0∞); reason: an empty class gives +∞, which satisfies every bound, as on p.42; same instances
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 25, Eq. (376), p.45

import Mathlib
import Definitions.Def_CubicProductLB_ProductRep
import Definitions.Def_CubicProductLB_minCost

namespace CubicProductLB.Supplement

/-- Theorem 25 (General degree-lifting inequality) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 25, Eq. (376), p.45). Fix `d ≥ 1` and a
prime `p > 3`. Let `f : ℕ → [0, ∞)` be nondecreasing with `L_d(k) ≥ f(k)` for every `k ≥ 1`. There is
`c_d > 0` such that for every `n ≥ 1` and every degree-at-most-`(d + 1)` representation of `F_{p,n}`
of occurrence cost `S`,
`S ≥ f(max(1, ⌊c_d · min(n, n^{(d+1)/d} / (S + 1)^{1/d})⌋))`.

**Formalization Note** `L_d` is the base mission's `minCost d p` in `ℕ∞` (`⊤` on an empty class),
compared with `f` in `ℝ≥0∞` through `ENNReal.ofReal`. `c_d` is chosen after `d`, `p` and `f`, as
printed. The powers are real powers and `⌊·⌋` is `Nat.floor`. -/
theorem theorem_25 (d : ℕ) (hd : 1 ≤ d) (p : ℕ) (hp : p.Prime) (h3 : 3 < p)
    (f : ℕ → ℝ) (hf0 : ∀ k, 0 ≤ f k) (hfm : Monotone f)
    (hL : ∀ k ≥ 1, ENNReal.ofReal (f k) ≤ ((minCost d p k : ℕ∞) : ENNReal)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n ≥ 1, ∀ r : ProductRep (d + 1) p n,
      f (max 1 ⌊c * min (n : ℝ)
        ((n : ℝ) ^ (((d : ℝ) + 1) / d) / ((r.cost : ℝ) + 1) ^ ((1 : ℝ) / d))⌋₊) ≤ (r.cost : ℝ) := by sorry

end CubicProductLB.Supplement
