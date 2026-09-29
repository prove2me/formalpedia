-- Prove2me | Theorems.Thm_AKR2008_rhoHat_11_val
-- name    : AKR2008.rhoHat_11_val
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:05:46.150087+00:00
-- url     : https://prove2.me/theorems/818c0bb4-3b74-4767-b681-80ecd0447c35
-- title:
--   Vertical entry of reference density matrix rhoHat is 1/2
-- statement:
--   The vertical diagonal entry of the reference unpolarized density matrix $\hat\rho$ equals $1/2$:
--
--   $$ \hat\rho_{11} = \tfrac{1}{2}. $$
--
--   This follows directly from the definition $\hat\rho = \frac{1}{2}(|0\rangle\langle 0| + |1\rangle\langle 1|)$ evaluated at the $(1, 1)$ entry.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), p. 064051-2, Sec. II, Eq. (3)

import Definitions.Def_AKR2008_Defs

namespace AKR2008

theorem rhoHat_11_val :
    rhoHat 1 1 = 1 / 2 := by sorry

end AKR2008
