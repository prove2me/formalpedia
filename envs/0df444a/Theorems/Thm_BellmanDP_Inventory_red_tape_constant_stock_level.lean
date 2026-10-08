-- Prove2me | Theorems.Thm_BellmanDP_Inventory_red_tape_constant_stock_level
-- name    : BellmanDP.Inventory.red_tape_constant_stock_level
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T16:42:48.021013+00:00
-- url     : https://prove2.me/theorems/6ca347fc-3e7e-4e67-b7cc-d75e5df3e690
-- title:
--   Chapter V, Theorem 4 — red-tape penalty: constant stock level at the last, absolute minimum of ψ
-- statement:
--   Add to the proportional penalty a fixed "red-tape" cost $q \ge 0$ for every stock-out:
--   $$f(x) = \min_{y\ge x}\Big[k(y-x) + a\Big(\int_y^\infty [p(s-y)+q]\varphi(s)\,ds + f(0)\int_y^\infty\varphi(s)\,ds + \int_0^y f(y-s)\varphi(s)\,ds\Big)\Big].$$
--   Assume the conditions of Theorem 1 ($k, p > 0$; $\varphi > 0$ on $(0,\infty)$, $\int_0^\infty\varphi = 1$, finite mean; $0 < a < 1$; $ap > k$) and let
--   $$\psi(y) = ky + a\Big[\int_y^\infty [p(s-y)+q]\varphi(s)\,ds - k\int_0^y (y-s)\varphi(s)\,ds\Big].$$
--   Suppose $\bar x \ge 0$ is an absolute minimizer of $\psi$ on $[0,\infty)$ and that $\psi$ has no later minimum: $\psi$ is nondecreasing on $[\bar x,\infty)$. Then the equation has exactly one solution among measurable functions bounded on $[0,\infty)$, and for every $x \ge 0$ its minimum is attained at
--   $$y = \bar x \ \text{ if } 0 \le x \le \bar x, \qquad y = x \ \text{ if } x \ge \bar x.$$
--
--   Unlike the case $q = 0$, the critical-level equation need not have a unique root; the constant-stock-level policy survives when its last minimum is the global one.
--
--   **Formalization Note** The book's hypothesis "the last minimum of $\psi$ is the absolute minimum in $0 \le y \le \infty$" is read as: $\bar x$ minimizes $\psi$ on $[0,\infty)$ and $\psi$ is monotone nondecreasing on $[\bar x,\infty)$. Since $\psi$ is continuous and tends to $+\infty$, a last local minimizer that is a global minimizer satisfies this. The book states no condition on $q$; $q \ge 0$ (a cost) is assumed. The bracket of (6), unbalanced in print, is closed at the end.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter V, § 9, Theorem 4, p. 171 (equation (9.1), p. 170)

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 9, Theorem 4, p. 171. Under the assumptions of
Theorem 1 on `a, k, p, φ` and `q ≥ 0`, suppose `x̄ ≥ 0` is an absolute minimizer of
`ψ(y) = ky + a [∫_y^∞ [p(s − y) + q] φ(s) ds − k ∫_0^y (y − s) φ(s) ds]` on `[0, ∞)` and that
`ψ` has no later minimum (it is monotone nondecreasing on `[x̄, ∞)`; this is the reading of
"the last minimum of ψ is the absolute minimum"). Then equation (9.1) has exactly one solution
in the class of measurable functions bounded on `[0, ∞)`, and for every `x ≥ 0` its minimum is
attained at `y = x̄` if `x ≤ x̄` and at `y = x` if `x ≥ x̄`. -/
theorem red_tape_constant_stock_level (k p q a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hq : 0 ≤ q) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p)
    (xbar : ℝ) (hxbar : 0 ≤ xbar)
    (hmin : ∀ y : ℝ, 0 ≤ y → psiQ k p q a φ xbar ≤ psiQ k p q a φ y)
    (hlast : MonotoneOn (psiQ k p q a φ) (Set.Ici xbar)) :
    ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invTq k p q a φ) f ∧
      (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invTq k p q a φ) g →
        Set.EqOn g f (Set.Ici 0)) ∧
      ∀ x : ℝ, 0 ≤ x →
        IsLeast (invTq k p q a φ f x '' Set.Ici x) (invTq k p q a φ f x (max x xbar)) := by sorry

end BellmanDP.Inventory
