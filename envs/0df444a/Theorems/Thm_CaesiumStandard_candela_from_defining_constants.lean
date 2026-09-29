-- Prove2me | Theorems.Thm_CaesiumStandard_candela_from_defining_constants
-- name    : CaesiumStandard.candela_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:28:32.575871+00:00
-- url     : https://prove2.me/theorems/a0e46b00-07c9-4c1f-93a2-1a90737d4cc4
-- title:
--   The candela from $h$, $\Delta\nu_{\mathrm{Cs}}$ and $K_{\mathrm{cd}}$
-- statement:
--   **The candela in terms of $h$, $\Delta\nu_{\mathrm{Cs}}$ and $K_{\mathrm{cd}}$.**
--
--   $$1\ \mathrm{cd} = \frac{10^{11}}{3.824\,339\,691\,519\,516\,481\,631\,301\,046\,05}\,
--   h\,\Delta\nu_{\mathrm{Cs}}^{2}\,K_{\mathrm{cd}},$$
--
--   i.e. the displayed expression has numerical value exactly $1$. This is the only base-unit relation
--   in which $\Delta\nu_{\mathrm{Cs}}$ occurs squared, the candela being a luminous intensity, i.e. a
--   power per solid angle, and the steradian being dimensionless.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Summary'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem candela_from_defining_constants :
    (1e11 / 3.82433969151951648163130104605) * (hPlanck * dnuCs ^ 2 * kcdLumEff) = 1 := by sorry

end CaesiumStandard
