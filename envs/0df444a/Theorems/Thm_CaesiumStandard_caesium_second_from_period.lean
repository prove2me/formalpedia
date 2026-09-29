-- Prove2me | Theorems.Thm_CaesiumStandard_caesium_second_from_period
-- name    : CaesiumStandard.caesium_second_from_period
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T16:12:38.378693+00:00
-- url     : https://prove2.me/theorems/4ce76aac-b8a5-4e1c-84d0-e96f5b8a9f9f
-- title:
--   $1\ \mathrm s = 9\,192\,631\,770\,\Delta t_{\mathrm{Cs}}$
-- statement:
--   **The 1967 definition of the second.**
--
--   The 13th CGPM (1967) defined the second as the duration of $9\,192\,631\,770$ periods of the
--   radiation corresponding to the transition between the two hyperfine levels of the ground state of
--   the caesium-133 atom. With $\Delta t_{\mathrm{Cs}} = 1/\Delta\nu_{\mathrm{Cs}}$ denoting that
--   period in seconds, the definition says
--
--   $$1\ \mathrm s = 9\,192\,631\,770\,\Delta t_{\mathrm{Cs}},\qquad\text{equivalently}\qquad
--   \Delta t_{\mathrm{Cs}} = \frac{1}{9\,192\,631\,770}\ \mathrm s .$$
--
--   Both forms are asserted: the product of the count and the period is exactly $1$, and the period is
--   exactly the reciprocal of the count.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Technical details'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem caesium_second_from_period :
    9192631770 * tCs = 1 ∧ tCs = 1 / 9192631770 := by sorry

end CaesiumStandard
