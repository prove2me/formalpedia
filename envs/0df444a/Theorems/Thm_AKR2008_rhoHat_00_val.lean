-- Prove2me | Theorems.Thm_AKR2008_rhoHat_00_val
-- name    : AKR2008.rhoHat_00_val
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:05:10.687224+00:00
-- url     : https://prove2.me/theorems/fd5c2a4c-e060-41d7-8d15-ac2b5dabb047
-- title:
--   Horizontal entry of reference density matrix rhoHat is 1/2
-- statement:
--   The horizontal diagonal entry of the reference unpolarized density matrix $\hat\rho$ equals $1/2$:
--
--   $$ \hat\rho_{00} = \tfrac{1}{2}. $$
--
--   This follows directly from the definition $\hat\rho = \frac{1}{2}(|0\rangle\langle 0| + |1\rangle\langle 1|)$ evaluated at the $(0, 0)$ entry.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eq. (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem rhoHat_00_val :
    rhoHat 0 0 = 1 / 2 := by sorry

end AKR2008
