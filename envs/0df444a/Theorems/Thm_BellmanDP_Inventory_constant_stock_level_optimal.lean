-- Prove2me | Theorems.Thm_BellmanDP_Inventory_constant_stock_level_optimal
-- name    : BellmanDP.Inventory.constant_stock_level_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T16:42:51.786915+00:00
-- url     : https://prove2.me/theorems/73de6aa8-6fe6-43f3-ba3b-02bb18c12418
-- title:
--   Chapter V, Theorem 1 (corrected (4b)) — the optimal inventory policy keeps a constant stock level
-- statement:
--   Let $k, p > 0$ be the unit ordering and penalty costs, $0 < a < 1$ the discount factor, and $\varphi$ a demand density: $\varphi(s) > 0$ for $s > 0$, $\int_0^\infty \varphi(s)\,ds = 1$, $\int_0^\infty s\varphi(s)\,ds < \infty$. Consider the optimal inventory equation
--   $$f(x) = \min_{y\ge x}\Big[k(y-x) + a\int_y^\infty p(s-y)\varphi(s)\,ds + af(0)\int_y^\infty\varphi(s)\,ds + a\int_0^y f(y-s)\varphi(s)\,ds\Big], \qquad x \ge 0.$$
--   It has exactly one solution $f$ among measurable functions bounded on $[0,\infty)$, and:
--
--   1. If $ap > k$, the equation
--   $$k = ap\int_y^\infty\varphi(s)\,ds + ak\int_0^y\varphi(s)\,ds$$
--   has exactly one root $\bar x \ge 0$, and for every $x \ge 0$ the minimum is attained at $y = \bar x$ when $0 \le x \le \bar x$ and at $y = x$ when $x \ge \bar x$: the optimal stock level is $\bar x$.
--   2. If $ap \le k$, the minimum is attained at $y = x$ for every $x \ge 0$: never order.
--
--   This is the chapter's main result: with proportional costs the optimal policy is described by one number, computed from the demand distribution alone.
--
--   **Formalization Note** The book prints (4b) as "for $x \ge \bar x$, $y = \bar x$", which would order a negative amount; the proof (p. 163, "the minimum occurs at $y = x$") and Theorem 4's rule (7) give $y = x$, which is what is stated. For example, with $x > \bar x$ the level $y = \bar x$ violates the constraint $y \ge x$. The equation is encoded with an infimum and attainment of the minimum is asserted at the stated order level. Uniqueness is in the class the proof names ("uniformly bounded functions over $x \ge 0$", p. 164), restricted to measurable functions.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter V, § 5, Theorem 1, pp. 159-160 (proof pp. 160-164)

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 5, Theorem 1, pp. 159-160, with (4b) corrected to
`y = x`. Let `k, p > 0`, `0 < a < 1` and let `φ` be a demand density (positive on `(0, ∞)`,
total mass 1, finite mean). Equation (5.1), `f(x) = Min_{y ≥ x} T(y, x, f)`, has exactly one
solution among measurable functions bounded on `[0, ∞)`, and:
* if `ap > k`, the equation `k = ap ∫_y^∞ φ + ak ∫_0^y φ` has exactly one root `x̄ ≥ 0`, and
  for every `x ≥ 0` the minimum is attained at `y = x̄` when `x ≤ x̄` and at `y = x` when
  `x ≥ x̄` (order up to `x̄`);
* if `ap ≤ k`, the minimum is attained at `y = x` for every `x ≥ 0` (never order). -/
theorem constant_stock_level_optimal (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ) (ha0 : 0 < a) (ha1 : a < 1) :
    (k < a * p →
      ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
        (∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar) ∧
        ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
          (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
            Set.EqOn g f (Set.Ici 0)) ∧
          ∀ x : ℝ, 0 ≤ x →
            IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x (max x xbar))) ∧
    (a * p ≤ k →
      ∃ f : ℝ → ℝ, BoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
        (∀ g : ℝ → ℝ, BoundedClass g → SolvesInf (invT k p a φ) g →
          Set.EqOn g f (Set.Ici 0)) ∧
        ∀ x : ℝ, 0 ≤ x → IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x x)) := by sorry

end BellmanDP.Inventory
