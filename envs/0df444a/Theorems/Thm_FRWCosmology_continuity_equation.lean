-- Prove2me | Theorems.Thm_FRWCosmology_continuity_equation
-- name    : FRWCosmology.continuity_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:46:18.890496+00:00
-- url     : https://prove2.me/theorems/6acb4580-8f0c-4c1c-a274-3a9e22b908ce
-- title:
--   Continuity equation $\dot\rho + 3H(\rho+p) = 0$
-- statement:
--   In any FRW universe with $G \neq 0$, at every time $t$ of the domain,
--
--   $$\dot\rho(t) + 3H(t)\bigl(\rho(t) + p(t)\bigr) = 0, \qquad H = \dot a / a .$$
--
--   This is the continuity equation, the cosmological counterpart of the conservation of
--   energy. It is a consequence of the two Friedmann equations: differentiating the first one in
--   time and substituting the second eliminates the curvature term, after which the factor
--   $8\pi G/3$ may be divided out — which is where $G \neq 0$ enters.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, p. 57, eq. (4.28)

import Definitions.Def_FRWUniverse

namespace FRWCosmology

theorem continuity_equation (U : FRWUniverse) (hG : U.G ≠ 0) (t : ℝ) (ht : t ∈ U.I) :
    U.rhodot t + 3 * U.H t * (U.rho t + U.p t) = 0 := by sorry

end FRWCosmology
