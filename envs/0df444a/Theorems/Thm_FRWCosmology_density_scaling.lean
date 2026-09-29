-- Prove2me | Theorems.Thm_FRWCosmology_density_scaling
-- name    : FRWCosmology.density_scaling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:46:54.818605+00:00
-- url     : https://prove2.me/theorems/dd0206df-9712-4890-ab89-bd5ced142892
-- title:
--   Density scaling $\rho \propto a^{-3(1+w)}$
-- statement:
--   Let an FRW universe with $G \neq 0$ carry a barotropic fluid with linear equation of state
--   $p = w\rho$, $w$ constant. Then for all times $s, t$ in the domain,
--
--   $$\rho(t)\,a(t)^{3(1+w)} \;=\; \rho(s)\,a(s)^{3(1+w)},$$
--
--   i.e. $\rho \propto a^{-3(1+w)}$. The real power is well defined because the scale factor is
--   positive. For dust ($w = 0$) this is $\rho \propto a^{-3}$ and for radiation ($w = 1/3$) it
--   is $\rho \propto a^{-4}$. The proof integrates the continuity equation, which is why
--   $G \neq 0$ is carried along.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, p. 63, eq. (4.38), with eq. (4.30) p. 60

import Definitions.Def_FRWUniverse

namespace FRWCosmology

theorem density_scaling (U : FRWUniverse) (hG : U.G ≠ 0) (w : ℝ) (hw : U.LinearEoS w)
    (s : ℝ) (hs : s ∈ U.I) (t : ℝ) (ht : t ∈ U.I) :
    U.rho t * U.a t ^ (3 * (1 + w)) = U.rho s * U.a s ^ (3 * (1 + w)) := by sorry

end FRWCosmology
