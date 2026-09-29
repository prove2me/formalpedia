-- Prove2me | Theorems.Thm_EinsteinFieldEquations_cosmological_constant_as_vacuum_energy
-- name    : EinsteinFieldEquations.cosmological_constant_as_vacuum_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:10:34.636684+00:00
-- url     : https://prove2.me/theorems/da5bcec8-bd9c-4506-ace1-b98225dd11eb
-- title:
--   The cosmological term as a vacuum stress–energy tensor
-- statement:
--   **Cosmological constant as vacuum energy.** Let $g$ be a metric, $T$ a stress–energy tensor, $\Lambda$ real and $\kappa \neq 0$. Then $g$ satisfies the field equations with cosmological constant $\Lambda$ and source $T$,
--
--   $$G_{ab} + \Lambda g_{ab} = \kappa T_{ab},$$
--
--   if and only if it satisfies the field equations with vanishing cosmological constant and the modified source $T_{ab} + T^{\text{vac}}_{ab}$, where
--
--   $$T^{\text{vac}}_{ab} \;=\; -\frac{\Lambda}{\kappa}\, g_{ab}.$$
--
--   This is the source's observation that the cosmological term can be moved algebraically to the other side of the equation and absorbed into the stress–energy tensor as a vacuum contribution, which is why "cosmological constant" and "vacuum energy" are used interchangeably.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Cosmological constant" (the vacuum stress-energy tensor $T^{\mathrm{vac}}_{\mu\nu} = -(\Lambda/\kappa) g_{\mu\nu}$)

import Definitions.Def_efe_geometry

namespace EinsteinFieldEquations

theorem cosmological_constant_as_vacuum_energy (g T : Tensor2Field) (Lam kappa : ℝ)
    (x : Coord) (hkappa : kappa ≠ 0) :
    SatisfiesEFE g Lam kappa T x ↔
      SatisfiesEFE g 0 kappa (fun y => T y - (Lam / kappa) • g y) x := by sorry

end EinsteinFieldEquations
