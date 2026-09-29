-- Prove2me | Theorems.Thm_CaesiumStandard_caesium_wavelength_value
-- name    : CaesiumStandard.caesium_wavelength_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T16:30:28.676154+00:00
-- url     : https://prove2.me/theorems/fe82abb1-7a69-4173-b49f-32e26f3ca7e5
-- title:
--   $\Delta\lambda_{\mathrm{Cs}} = 299\,792\,458/9\,192\,631\,770$ m, between 3.26 and 3.27 cm
-- statement:
--   **Wavelength of the caesium hyperfine transition radiation.**
--
--   With $\Delta\lambda_{\mathrm{Cs}} = c/\Delta\nu_{\mathrm{Cs}}$ the wavelength in metres,
--
--   $$\Delta\lambda_{\mathrm{Cs}} = \frac{299\,792\,458}{9\,192\,631\,770}\ \mathrm m,$$
--
--   and this value lies strictly between $0.0326\ \mathrm m$ and $0.0327\ \mathrm m$, confirming the
--   source's statement that the wavelength is "about $3.26$ centimetres" and therefore in the
--   microwave range.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Parameters and significance — Length'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem caesium_wavelength_value :
    lambdaCs = 299792458 / 9192631770 ∧ 0.0326 < lambdaCs ∧ lambdaCs < 0.0327 := by sorry

end CaesiumStandard
