-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousOn_piDs
-- name    : FiniteEnergyPlane.continuousOn_piDs
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:35:45.835165+00:00
-- url     : https://prove2.me/theorems/5e6f7459-fc58-43dd-b713-2f4430341411
-- title:
--   Continuity of $\pi\partial_s u$ in the global frame of $\xi$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Liouville form $\lambda_0$ and contact structure $\xi$, and let $U\subset\mathbb{C}$ be open. If $u:\mathbb{C}\to\mathbb{R}^4$ is smooth and nonvanishing on $U$, then the function
--   $$z\mapsto \Xi_{w(z)}\big(\pi\,\partial_s w(z)\big)\in\mathbb{C},\qquad w=\mathrm{pr}\circ u,$$
--   is continuous on $U$. Here $\pi:TS\to\xi$ is the projection along the Reeb field and $\Xi$ gives the coordinates in Hryniewicz's global frame of $\xi$.
--
--   This makes $\pi\partial_s u$, viewed as a complex function, available to topological arguments, such as computing winding numbers along circles in $U$.
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1` and the function is `piDs H u`. Only smoothness and non-vanishing of `u` on `U` are assumed (no holomorphicity or energy bound).
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `u` is smooth and nonvanishing on an open set `U ⊆ ℂ`, then the `ξ`-component
`π ∂ₛ(proj ∘ u)` in the global frame of `ξ`, `piDs H u`, is continuous on `U`. -/
theorem continuousOn_piDs (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (U : Set ℂ)
    (hU : IsOpen U) (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    ContinuousOn (piDs H u) U := by
  sorry

end FiniteEnergyPlane
