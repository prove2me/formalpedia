-- Prove2me | Theorems.Thm_BellmanDP_Inventory_finite_horizon_stock_levels
-- name    : BellmanDP.Inventory.finite_horizon_stock_levels
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T16:42:50.055952+00:00
-- url     : https://prove2.me/theorems/12a5d968-0059-4a75-939e-78532d94ed9a
-- title:
--   Chapter V, Theorem 3 — finite horizon: order-up-to levels that increase with the number of stages
-- statement:
--   Consider the undiscounted $n$-stage inventory process (Chapter V, Eq. (7.2)):
--   $$f_1(x) = \min_{y\ge x}\Big[k(y-x) + p\int_y^\infty (s-y)\varphi(s)\,ds\Big],$$
--   $$f_{n+1}(x) = \min_{y\ge x}\Big[k(y-x) + p\int_y^\infty (s-y)\varphi(s)\,ds + f_n(0)\int_y^\infty \varphi(s)\,ds + \int_0^y f_n(y-s)\varphi(s)\,ds\Big].$$
--   Assume $0 < k < p$ and that $\varphi$ is a demand density ($\varphi > 0$ on $(0,\infty)$, $\int_0^\infty\varphi = 1$, finite mean). Then there are levels $\bar x_1 \le \bar x_2 \le \cdots$, all $\ge 0$, such that for every $n$ and every $x \ge 0$ the minimum defining $f_n(x)$ is attained at
--   $$y = \bar x_n \ \text{ if } x \le \bar x_n, \qquad y = x \ \text{ if } x \ge \bar x_n.$$
--
--   With finitely many stages the optimal policy is again a constant stock level at each stage, and the level rises as more stages remain.
--
--   **Formalization Note** $f_n$ is obtained from $f_0 = 0$ by the discounted recursion with discount factor $1$; the Lean sequence `xbar` is indexed from $0$, so `xbar n` is the level $\bar x_{n+1}$ of $f_{n+1}$. The book's hypothesis is "the natural assumption $p > k$"; $k > 0$ and the density conditions of Theorem 1 are taken from the chapter's setting (the proof uses $f_1'' = p\varphi > 0$).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter V, § 7, Theorem 3, p. 166 (recurrence (7.2), p. 166)

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 7, Theorem 3, p. 166. Undiscounted finite process
(7.2): `f₁(x) = Min_{y ≥ x} [k(y − x) + p ∫_y^∞ (s − y) φ(s) ds]` and
`f_{n+1}(x) = Min_{y ≥ x} [k(y − x) + p ∫_y^∞ (s − y) φ(s) ds + f_n(0) ∫_y^∞ φ(s) ds
+ ∫_0^y f_n(y − s) φ(s) ds]`; in Lean `f_{n+1} = invIter k p 1 φ 0 (n + 1)` (starting from
`f₀ = 0`, discount `a = 1`). If `0 < k < p` and `φ` is a demand density, then for each
`n ≥ 1` there is a level `x̄_n ≥ 0` (here `xbar n` is the level of `f_{n+1}`, i.e. the book's
`x̄_{n+1}`) such that ordering up to `max(x, x̄_n)` attains the minimum defining `f_n(x)` for
every `x ≥ 0`, and the levels are monotone increasing in `n`. -/
theorem finite_horizon_stock_levels (k p : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hkp : k < p) (hφ : DemandDensity φ) :
    ∃ xbar : ℕ → ℝ, Monotone xbar ∧ (∀ n : ℕ, 0 ≤ xbar n) ∧
      ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
        IsLeast (invT k p 1 φ (invIter k p 1 φ (fun _ => 0) n) x '' Set.Ici x)
          (invT k p 1 φ (invIter k p 1 φ (fun _ => 0) n) x (max x (xbar n))) := by sorry

end BellmanDP.Inventory
