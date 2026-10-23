-- Prove2me | Theorems.Thm_DoubleAuctionEff_Repeated_assumption5_le_radius
-- name    : DoubleAuctionEff.Repeated.assumption5_le_radius
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:01.225987+00:00
-- url     : https://prove2.me/theorems/dcc4c262-1fa1-41b0-84e2-2ae0c885cbbe
-- title:
--   p. 18 — for concave u, the inequality of Assumption 5 at radius r gives u(x + r′g) ≥ u(x) + δ r′ for every r′ ∈ (0, r] and x ∈ 𝔹(r)
-- statement:
--   Let $u:\mathbb R^J\to[-\infty,+\infty]$ be concave, $g\in\mathbb R^J$, and $r,\delta\in\mathbb R$. Suppose
--   $$u(x+rg)\ge u(x)+\delta r\qquad\text{for all }x\in\mathbb B(r).$$
--   Then for every $x\in\mathbb B(r)$ and every $r'\in(0,r]$,
--   $$u(x+r'g)\ge u(x)+\delta r'.$$
--
--   This lets Assumption 5 be applied with the agent's surplus in an auction in place of the radius.
--
--   **Formalization Note** $\mathbb B(r)$ is the closed sup-norm ball of radius $r$ about the origin. The inequalities are in $[-\infty,+\infty]$.
-- source:
--   T. Pennanen, Efficient allocations in double auction markets, arXiv:2001.02071v2, p. 18, the paragraph after Assumption 5

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

namespace DoubleAuctionEff.Repeated
theorem assumption5_le_radius {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g : J → ℝ) (r δ : ℝ) (hconc : IsConcaveE u) (h5 : Assumption5At u g r δ) : ∀ x ∈ Metric.closedBall (0 : J → ℝ) r, ∀ r' : ℝ, 0 < r' → r' ≤ r → u x + ((δ * r' : ℝ) : EReal) ≤ u (x + r' • g) := by sorry
end DoubleAuctionEff.Repeated
