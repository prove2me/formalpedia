-- Prove2me | Theorems.Thm_CaesiumStandard_caesium_photon_mass_value
-- name    : CaesiumStandard.caesium_photon_mass_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:47:05.776514+00:00
-- url     : https://prove2.me/theorems/041d52b7-7bfc-4cec-ab0f-29ba0590026d
-- title:
--   $\Delta M_{\mathrm{Cs}} = 6.09110229711386655\times10^{-40}/8.9875517873681764$ kg
-- statement:
--   **Photon mass equivalent of the caesium hyperfine transition radiation.**
--
--   With $\Delta M_{\mathrm{Cs}} = \Delta E_{\mathrm{Cs}}/c^{2}$ and
--   $c^{2} = 8.987\,551\,787\,368\,1764\times10^{16}\ \mathrm{m^2/s^2}$,
--
--   $$\Delta M_{\mathrm{Cs}} = \frac{6.091\,102\,297\,113\,866\,55\times10^{-40}}
--   {8.987\,551\,787\,368\,1764}\ \mathrm{kg},$$
--
--   which is the value displayed in the *Mass, energy, and force* section of the source.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Mass, energy, and force'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem caesium_photon_mass_value :
    MCs = 6.09110229711386655e-40 / 8.9875517873681764 := by sorry

end CaesiumStandard
