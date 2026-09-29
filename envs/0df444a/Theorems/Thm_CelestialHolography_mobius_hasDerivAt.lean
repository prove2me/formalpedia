-- Prove2me | Theorems.Thm_CelestialHolography_mobius_hasDerivAt
-- name    : CelestialHolography.mobius_hasDerivAt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T02:08:28.459175+00:00
-- url     : https://prove2.me/theorems/c7dc6f65-dc8b-4e73-aa25-e41c90003869
-- title:
--   Eq. (13): $\partial z'/\partial z=(cz+d)^{-2}$ for $z'=(az+b)/(cz+d)$
-- statement:
--   For $M\in SL(2,\mathbb C)$ and $z\in\mathbb C$ with $cz+d\neq0$, the Möbius map $w\mapsto (aw+b)/(cw+d)$ is complex-differentiable at $z$ with
--   $$\frac{\partial z'}{\partial z}=\frac1{(cz+d)^2}.$$
--   Hence $|\partial z'/\partial z|^{-1}=|cz+d|^2$, the conformal factor in the goal theorem and in the Jacobian factors of the primary transformation law (13).
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem mobius_hasDerivAt (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) (z : ℂ)
    (hz : M 1 0 * z + M 1 1 ≠ 0) :
    HasDerivAt (mobius M) (1 / (M 1 0 * z + M 1 1) ^ 2) z := by sorry

end CelestialHolography
