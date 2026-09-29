-- Prove2me | Theorems.Thm_CaesiumStandard_kelvin_from_defining_constants
-- name    : CaesiumStandard.kelvin_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:21:41.159507+00:00
-- url     : https://prove2.me/theorems/63e79595-72b4-4cea-a1c0-6ed11b180997
-- title:
--   The kelvin from $h$, $\Delta\nu_{\mathrm{Cs}}$ and $k$
-- statement:
--   **The kelvin in terms of $h$, $\Delta\nu_{\mathrm{Cs}}$ and $k$.**
--
--   $$1\ \mathrm K = \frac{13.806\,49}{6.091\,102\,297\,113\,866\,55}\,
--   \frac{h\,\Delta\nu_{\mathrm{Cs}}}{k},$$
--
--   i.e. the displayed expression has numerical value exactly $1$. Equivalently, the caesium photon
--   energy is $6.091\,102\,297\,113\,866\,55/13.806\,49$ of the energy $k\cdot 1\ \mathrm K$.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Summary'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem kelvin_from_defining_constants :
    (13.80649 / 6.09110229711386655) * (hPlanck * dnuCs / kBoltzmann) = 1 := by sorry

end CaesiumStandard
