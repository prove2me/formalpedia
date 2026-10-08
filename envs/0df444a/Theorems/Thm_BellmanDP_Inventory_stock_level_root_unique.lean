-- Prove2me | Theorems.Thm_BellmanDP_Inventory_stock_level_root_unique
-- name    : BellmanDP.Inventory.stock_level_root_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T16:42:25.259987+00:00
-- url     : https://prove2.me/theorems/e6bbc98b-a64e-4a13-a81e-6193d1ebb260
-- title:
--   Chapter V, Eq. (5.8) — the critical stock level is the unique root of $\int_0^y\varphi = (ap-k)/a(p-k)$
-- statement:
--   Let $k, p > 0$, $0 < a < 1$ with $ap > k$, and let $\varphi$ be a demand density: $\varphi(s) > 0$ for $s > 0$, $\int_0^\infty \varphi(s)\,ds = 1$ and $\int_0^\infty s\varphi(s)\,ds < \infty$. Consider the critical-level equation of Chapter V, Theorem 1,
--   $$k = ap\int_y^\infty \varphi(s)\,ds + ak\int_0^y \varphi(s)\,ds, \qquad y \ge 0.$$
--   Then
--
--   1. a level $y \ge 0$ solves it exactly when
--   $$\int_0^y \varphi(s)\,ds = \frac{ap-k}{a(p-k)};$$
--   2. the equation has exactly one root $\bar x \ge 0$.
--
--   The root $\bar x$ is the constant stock level of the optimal policy in Chapter V, Theorem 1; this is the statement that makes "let $\bar x$ be the unique root of (3)" well defined.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter V, § 5, Eqs. (5.7)-(5.8), p. 161 (equation (3) of Theorem 1, p. 160)

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. V, § 5, Eqs. (5.3), (5.7)-(5.8), p. 161: under
hypotheses (2a)-(2d) of Theorem 1, a level `y ≥ 0` is a root of
`k = ap ∫_y^∞ φ + ak ∫_0^y φ` exactly when `∫_0^y φ(s) ds = (ap − k)/a(p − k)`, and this
equation has exactly one root `x̄ ≥ 0`. -/
theorem stock_level_root_unique (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 < p) (hφ : DemandDensity φ)
    (ha0 : 0 < a) (ha1 : a < 1) (hapk : k < a * p) :
    (∀ y : ℝ, 0 ≤ y →
      (StockLevelRoot k p a φ y ↔ (∫ s in (0 : ℝ)..y, φ s) = (a * p - k) / (a * (p - k)))) ∧
    ∃ xbar : ℝ, 0 ≤ xbar ∧ StockLevelRoot k p a φ xbar ∧
      ∀ y : ℝ, 0 ≤ y → StockLevelRoot k p a φ y → y = xbar := by sorry

end BellmanDP.Inventory
