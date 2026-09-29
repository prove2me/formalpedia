-- Prove2me | Theorems.Thm_CaesiumStandard_optical_units_from_caesium_parameters
-- name    : CaesiumStandard.optical_units_from_caesium_parameters
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:40:36.342989+00:00
-- url     : https://prove2.me/theorems/f99b3264-4515-4099-b37b-669c950c2fb3
-- title:
--   The 540 THz reference radiation, the lumen and the lux
-- statement:
--   **The $540\ \mathrm{THz}$ reference radiation, the lumen and the lux.**
--
--   The optical units are defined through monochromatic radiation of frequency
--   $\nu_{\mathrm{opt}} = 540\ \mathrm{THz}$ with luminous efficacy
--   $K_{\mathrm{cd}} = 683\ \mathrm{lm/W}$. Its period, wavelength, photon energy and luminous energy
--   per photon are exactly
--
--   $$t_{\mathrm{opt}} = \frac{50}{27}\ \mathrm{fs},\qquad
--   \lambda_{\mathrm{opt}} = \frac{14.989\,622\,9}{27}\ \mathrm{\mu m},\qquad
--   E_{\mathrm{opt}} = 3.578\,077\,881\times10^{-19}\ \mathrm J,$$
--
--   $$K_{\mathrm{cd}}\,E_{\mathrm{opt}} = 2.443\,827\,192\,723\times10^{-16}\ \mathrm{lm\,s},$$
--
--   and the *Optical units* section's expressions for the lumen and the lux,
--
--   $$1\ \mathrm{lm} = \frac{10^{6}}{2.246\,520\,349\,221\,536\,260\,971}\,
--   K_{\mathrm{cd}}\,E_{\mathrm{opt}}\,\Delta\nu_{\mathrm{Cs}},\qquad
--   1\ \mathrm{lx} = \frac{8.987\,551\,787\,368\,1764\times10^{2}}
--   {1.898\,410\,313\,566\,852\,566\,340\,456\,048\,807\,087\,002\,459}\,
--   \frac{K_{\mathrm{cd}}\,E_{\mathrm{opt}}\,\Delta\nu_{\mathrm{Cs}}}{\Delta\lambda_{\mathrm{Cs}}^{2}},$$
--
--   each have numerical value exactly $1$.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Optical units'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem optical_units_from_caesium_parameters :
    tOpt = (50 / 27) * 1e-15
    ∧ lambdaOpt = (14.9896229 / 27) * 1e-6
    ∧ EOpt = 3.578077881e-19
    ∧ luminousEnergyPerPhotonOpt = 2.443827192723e-16
    ∧ (1e6 / 2.246520349221536260971) * (luminousEnergyPerPhotonOpt * dnuCs) = 1
    ∧ (8.9875517873681764e2 / 1.898410313566852566340456048807087002459)
        * (luminousEnergyPerPhotonOpt * dnuCs / lambdaCs ^ 2) = 1 := by sorry

end CaesiumStandard
