-- Prove2me | Theorems.Thm_CaesiumStandard_energy_force_pressure_units_from_caesium_parameters
-- name    : CaesiumStandard.energy_force_pressure_units_from_caesium_parameters
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:30:14.545511+00:00
-- url     : https://prove2.me/theorems/fed86397-bb32-4f76-a9c3-6c3943a2c481
-- title:
--   Joule, watt, newton, pascal and gray from the caesium radiation parameters
-- statement:
--   **Joule, watt, newton, pascal and gray from the caesium radiation parameters.**
--
--   Writing $\Delta E_{\mathrm{Cs}} = h\,\Delta\nu_{\mathrm{Cs}}$,
--   $\Delta\lambda_{\mathrm{Cs}} = c/\Delta\nu_{\mathrm{Cs}}$ and
--   $\Delta M_{\mathrm{Cs}} = \Delta E_{\mathrm{Cs}}/c^{2}$, the *Mass, energy, and force* section of
--   the source gives
--
--   $$1\ \mathrm J = \frac{10^{24}}{6.091\,102\,297\,113\,866\,55}\,\Delta E_{\mathrm{Cs}},\qquad
--   1\ \mathrm W = \frac{10^{14}}{5.599\,326\,049\,076\,890\,895\,507\,029\,35}\,
--   \Delta E_{\mathrm{Cs}}\,\Delta\nu_{\mathrm{Cs}},$$
--
--   $$1\ \mathrm N = \frac{2.997\,924\,58\times10^{22}}{5.599\,326\,049\,076\,890\,895\,507\,029\,35}\,
--   \frac{\Delta E_{\mathrm{Cs}}}{\Delta\lambda_{\mathrm{Cs}}},$$
--
--   $$1\ \mathrm{Pa} = \frac{2.694\,400\,241\,737\,398\,953\,933\,5912\times10^{19}}
--   {4.731\,681\,297\,378\,209\,131\,892\,876\,988\,924\,868\,114\,516\,206\,15}\,
--   \frac{\Delta E_{\mathrm{Cs}}}{\Delta\lambda_{\mathrm{Cs}}^{3}},\qquad
--   1\ \mathrm{Gy} = \frac{1}{89\,875\,517\,873\,681\,764}\,
--   \frac{\Delta E_{\mathrm{Cs}}}{\Delta M_{\mathrm{Cs}}}.$$
--
--   Each of the five displayed expressions is asserted to have numerical value exactly $1$.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Mass, energy, and force'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem energy_force_pressure_units_from_caesium_parameters :
    (1e24 / 6.09110229711386655) * ECs = 1
    ∧ (1e14 / 5.59932604907689089550702935) * (ECs * dnuCs) = 1
    ∧ (2.99792458e22 / 5.59932604907689089550702935) * (ECs / lambdaCs) = 1
    ∧ (2.6944002417373989539335912e19
        / 4.73168129737820913189287698892486811451620615) * (ECs / lambdaCs ^ 3) = 1
    ∧ (1 / 89875517873681764) * (ECs / MCs) = 1 := by sorry

end CaesiumStandard
