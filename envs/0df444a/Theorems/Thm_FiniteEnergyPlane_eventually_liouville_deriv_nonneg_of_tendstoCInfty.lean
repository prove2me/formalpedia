-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eventually_liouville_deriv_nonneg_of_tendstoCInfty
-- name    : FiniteEnergyPlane.eventually_liouville_deriv_nonneg_of_tendstoCInfty
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T18:14:27.506133+00:00
-- url     : https://prove2.me/theorems/0d5292e5-6a25-4ab7-b2d7-49d5c9e1c0c8
-- title:
--   Loops converging to a Reeb orbit have nonnegative action integrand
-- statement:
--   Let $S = H^{-1}(1)$ be a strictly star-shaped level with Liouville form $\lambda_0$, $Q = (x, T)$ a periodic Reeb orbit on $S$, and $c \in \mathbb{R}$. If maps $l_k : \mathbb{R} \to \mathbb{R}^{2n+2}$ converge in $C^\infty$, uniformly on $\mathbb{R}$, to $t \mapsto x(Tt + c)$, then for all large $k$
--   $$\lambda_0(l_k(t))\big(l_k'(t)\big) \ge 0 \quad \text{for all } t \in \mathbb{R}.$$
--
--   This gives a pointwise sign for the action density on large circles of finite-energy planes, whose loops subconverge to periodic orbits.
--
--   Formalization Note: `TendstoCInfty` is uniform convergence on $\mathbb{R}$ of every derivative. The maps $l_k$ need not lie on $S$.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If loops `l k` converge in `C^∞` to a reparametrized periodic Reeb orbit `t ↦ x(T t + c)`, then
for all large `k` the action integrand `λ₀(l k t)(l k' t)` is nonnegative for every `t`. -/
theorem eventually_liouville_deriv_nonneg_of_tendstoCInfty {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (l : ℕ → ℝ → V n) (Q : ReebOrbit H) (c : ℝ)
    (hconv : TendstoCInfty l (fun t => Q.x (Q.T * t + c))) :
    ∀ᶠ k in atTop, ∀ t, 0 ≤ liouville (l k t) (deriv (l k) t) := by
  sorry

end FiniteEnergyPlane
