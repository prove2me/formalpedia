-- Prove2me | Theorems.Thm_FiniteEnergyPlane_im_conj_xiCoordC_mul
-- name    : FiniteEnergyPlane.im_conj_xiCoordC_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T21:17:00.096139+00:00
-- url     : https://prove2.me/theorems/2583ae07-336f-4dac-a7d5-423691fa0286
-- title:
--   The global-frame coordinates of $\xi$ are symplectic
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $x\in S$, and $\psi_x:\xi_x\to\mathbb{C}$ the coordinates in Hryniewicz's global frame of $\xi$. Then for all $a,b\in\xi_x$
--   $$\operatorname{Im}\big(\overline{\psi_x(a)}\,\psi_x(b)\big)=\omega_0(a,b).$$
--   In particular $\psi_x$ is an orientation-preserving isomorphism from $(\xi_x,\omega_0)$ to $\mathbb{C}$ with its standard symplectic form.
--
--   **Formalization Note** $\psi_x$ is `xiCoordC H x`, $\xi_x$ membership is `IsInXi H x`, and $\omega_0$ is `omega0` on `V 1`.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2 (global symplectic frame of the contact structure)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

/-- For `x ∈ S = H⁻¹(1)` and `a, b ∈ ξ_x`, the global-frame coordinates `ψ_x = xiCoordC H x` satisfy
`Im(conj ψ_x(a) · ψ_x(b)) = ω₀(a, b)`. -/
theorem im_conj_xiCoordC_mul (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V 1}
    (hx : H x = 1) {a b : V 1} (ha : IsInXi H x a) (hb : IsInXi H x b) :
    (starRingEnd ℂ (xiCoordC H x a) * xiCoordC H x b).im = omega0 a b := by
  sorry

end FiniteEnergyPlane
