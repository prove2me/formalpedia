-- Prove2me | Theorems.Thm_CaesiumStandard_ampere_from_defining_constants
-- name    : CaesiumStandard.ampere_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:14:09.984279+00:00
-- url     : https://prove2.me/theorems/6f9a72dc-02a1-4b58-8015-f88413aa551d
-- title:
--   The ampere from $e$ and $\Delta\nu_{\mathrm{Cs}}$
-- statement:
--   **The ampere in terms of $e$ and $\Delta\nu_{\mathrm{Cs}}$.**
--
--   $$1\ \mathrm A = \frac{10^{9}}{1.472\,821\,982\,686\,006\,218}\,e\,\Delta\nu_{\mathrm{Cs}},$$
--
--   i.e. the displayed expression has numerical value exactly $1$. The coefficient records that
--   $e\,\Delta\nu_{\mathrm{Cs}} = 1.472\,821\,982\,686\,006\,218\times10^{-9}\ \mathrm A$, so one
--   ampere is that many elementary charges per caesium period.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Summary'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem ampere_from_defining_constants :
    (1e9 / 1.472821982686006218) * (eCharge * dnuCs) = 1 := by sorry

end CaesiumStandard
