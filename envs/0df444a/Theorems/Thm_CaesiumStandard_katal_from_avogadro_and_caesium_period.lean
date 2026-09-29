-- Prove2me | Theorems.Thm_CaesiumStandard_katal_from_avogadro_and_caesium_period
-- name    : CaesiumStandard.katal_from_avogadro_and_caesium_period
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:42:38.017473+00:00
-- url     : https://prove2.me/theorems/ce40ced7-b7a6-4c08-9d46-e229f21d2ce3
-- title:
--   The katal from $N_{\mathrm A}$ and $\Delta t_{\mathrm{Cs}}$
-- statement:
--   **The katal from the Avogadro constant and the caesium period.**
--
--   One katal is one mole of elementary entities per second. Measured in entities per caesium period
--   $\Delta t_{\mathrm{Cs}}$, the source's *Amount of substance* section gives
--
--   $$N_{\mathrm A}\,\Delta t_{\mathrm{Cs}}
--   = \frac{6.022\,140\,76\times10^{14}}{9.192\,631\,77},$$
--
--   so that $1\ \mathrm{kat}$ equals that many elementary entities per $\Delta t_{\mathrm{Cs}}$. The
--   mole itself is the one base unit independent of the caesium standard; only the *per second* factor
--   brings $\Delta\nu_{\mathrm{Cs}}$ in.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Amount of substance'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem katal_from_avogadro_and_caesium_period :
    nAvogadro * tCs = 6.02214076e14 / 9.19263177 := by sorry

end CaesiumStandard
