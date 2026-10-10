-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_local_energy_momentum_conservation
-- name    : EinsteinFieldEquationsD.local_energy_momentum_conservation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:20:49.208348+00:00
-- url     : https://prove2.me/theorems/0281a370-2720-4ab5-886f-424c8a36a012
-- title:
--   Einstein field equations imply local conservation of energy–momentum
-- statement:
--   **Local conservation of energy and momentum.** Let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$, let $G>0$ (Newton's constant) and $c>0$ (speed of light), put $\kappa=8\pi G/c^4$, and suppose the Einstein field equations
--   $$G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa T_{\mu\nu}$$
--   hold on $U$. Then the stress–energy tensor is covariantly conserved on $U$:
--   $$\nabla_\beta T^{\alpha\beta}=0,$$
--   formalized in the index-lowered form $g^{\beta\lambda}\nabla_\lambda T_{\alpha\beta}=0$.
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Features — Conservation of energy and momentum'

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem local_energy_momentum_conservation {D : ℕ} (g T : Tensor2 D) (U : Set (Coord D)) (Λ G c : ℝ)
    (hg : IsMetricOn g U) (hG : 0 < G) (hc : 0 < c)
    (hEFE : EinsteinFieldEquationsOn g T Λ (einsteinGravitationalConstant G c) U) :
    ∀ x ∈ U, ∀ a : Fin D, divergence g T x a = 0 := by sorry

end EinsteinFieldEquationsD
