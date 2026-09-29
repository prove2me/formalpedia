-- Prove2me | Theorems.Thm_ElementaryCharge_faraday_constant_exact_value
-- name    : ElementaryCharge.faraday_constant_exact_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T16:31:23.936713+00:00
-- url     : https://prove2.me/theorems/1803a71e-d21b-44c8-998d-e3cac2fdec23
-- title:
--   Exact SI value of the Faraday constant
-- statement:
--   At the 2019 SI fixed values of the Avogadro constant and of the elementary charge, the Faraday constant has the exact value $F = N_\mathrm{A}e = 96\,485.3321233100184\ \mathrm{C\,mol^{-1}}$. Both sides are exact rationals, so this is an identity and not a numerical approximation.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib
import Definitions.Def_elementary_charge_si_constants

namespace ElementaryCharge

theorem faraday_constant_exact_value :
    faradayConstant avogadroSI eSI = 964853321233100184 / 10 ^ 13 := by sorry

end ElementaryCharge
