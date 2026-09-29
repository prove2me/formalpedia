-- Prove2me | Theorems.Thm_CaesiumStandard_caesium_photon_energy_value
-- name    : CaesiumStandard.caesium_photon_energy_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:13:30.042635+00:00
-- url     : https://prove2.me/theorems/27f48e06-af68-4254-a982-0c0064f4eac0
-- title:
--   $\Delta E_{\mathrm{Cs}} = 6.09110229711386655\times10^{-24}$ J
-- statement:
--   **Photon energy of the caesium hyperfine transition radiation.**
--
--   With $\Delta E_{\mathrm{Cs}} = h\,\Delta\nu_{\mathrm{Cs}}$, the fixed values
--   $h = 6.626\,070\,15\times10^{-34}\ \mathrm{J\,s}$ and
--   $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$ give the exact energy
--
--   $$\Delta E_{\mathrm{Cs}} = 6.091\,102\,297\,113\,866\,55\times10^{-24}\ \mathrm J .$$
--
--   The product of the two exact decimals terminates, so the equality is exact rather than rounded.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Mass, energy, and force'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem caesium_photon_energy_value :
    ECs = 6.09110229711386655e-24 := by sorry

end CaesiumStandard
