-- Prove2me | Theorems.Thm_CaesiumStandard_kilogram_from_defining_constants
-- name    : CaesiumStandard.kilogram_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:57:12.311291+00:00
-- url     : https://prove2.me/theorems/905549cb-c203-4261-9431-01480748294d
-- title:
--   The kilogram from $h$, $\Delta\nu_{\mathrm{Cs}}$ and $c$
-- statement:
--   **The kilogram in terms of $h$, $\Delta\nu_{\mathrm{Cs}}$ and $c$.**
--
--   $$1\ \mathrm{kg} = \frac{8.987\,551\,787\,368\,1764\times10^{40}}{6.091\,102\,297\,113\,866\,55}\,
--   \frac{h\,\Delta\nu_{\mathrm{Cs}}}{c^{2}},$$
--
--   i.e. the displayed expression has numerical value exactly $1$. The coefficient is the reciprocal of
--   the photon mass equivalent $\Delta M_{\mathrm{Cs}}$ expressed in kilograms: the denominator is the
--   mantissa of the caesium photon energy in joules, the numerator that of $c^{2}$, shifted by the
--   appropriate power of ten.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Summary'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem kilogram_from_defining_constants :
    (8.9875517873681764e40 / 6.09110229711386655) * (hPlanck * dnuCs / cLight ^ 2) = 1 := by sorry

end CaesiumStandard
