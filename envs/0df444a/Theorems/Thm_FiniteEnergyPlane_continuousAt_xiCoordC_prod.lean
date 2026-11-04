-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousAt_xiCoordC_prod
-- name    : FiniteEnergyPlane.continuousAt_xiCoordC_prod
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T10:10:10.583194+00:00
-- url     : https://prove2.me/theorems/dbc8a7c0-03c9-4b98-8e87-6c50107ce6e7
-- title:
--   The global-frame coordinates of $\xi$ depend continuously on the base point and the vector
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, and let $\Xi_x:\mathbb{R}^4\to\mathbb{C}$ be the coordinate map of Hryniewicz's global frame $Z_1(x),Z_2(x)$ of $\xi$, i.e. $\Xi_x(v)=\omega_0(v,Z_2(x))+i\,\omega_0(Z_1(x),v)$. Then the map
--   $$\mathbb{R}^4\times\mathbb{R}^4\to\mathbb{C},\qquad (x,v)\mapsto \Xi_x(v)$$
--   is jointly continuous at every point $(x,v)$ with $x\in S$.
--
--   This lets the global-frame coordinates of a $\xi$-valued section be compared along nearby base points, uniformly on compact sets such as the image of a periodic Reeb orbit.
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`, and $\Xi_x(v)$ is `xiCoordC H x v`. The hypothesis $x\in S$ is `H x = 1`. Continuity is `ContinuousAt` on the product `V 1 × V 1` at `(x, v)`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4 (the global frame of $\xi$ on a star-shaped level)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Topology

/-- Let `S = H⁻¹(1)` be a strictly star-shaped level. The global-frame coordinate map
`(x, v) ↦ xiCoordC H x v` is jointly continuous at every point `(x, v)` with `x ∈ S`. -/
theorem continuousAt_xiCoordC_prod (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {x v : V 1}
    (hx : H x = 1) : ContinuousAt (fun p : V 1 × V 1 => xiCoordC H p.1 p.2) (x, v) := by
  sorry

end FiniteEnergyPlane
