-- Prove2me | Theorems.Thm_CaesiumStandard_si_base_units_from_defining_constants
-- name    : CaesiumStandard.si_base_units_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T15:57:46.26914+00:00
-- url     : https://prove2.me/theorems/a4273253-0269-4da4-9bec-b0ad9ce517d8
-- title:
--   The seven SI base units expressed in the SI defining constants
-- statement:
--   **The seven SI base units in terms of the SI defining constants.**
--
--   The 2019 SI fixes exact values for $\Delta\nu_{\mathrm{Cs}}$, $c$, $h$, $e$, $k$, $N_{\mathrm A}$
--   and $K_{\mathrm{cd}}$. Expressing each base unit explicitly in those constants, as in the
--   *Summary* section of the source, gives
--
--   $$
--   1\ \mathrm s = \frac{9\,192\,631\,770}{\Delta\nu_{\mathrm{Cs}}},\qquad
--   1\ \mathrm m = \frac{9\,192\,631\,770}{299\,792\,458}\,\frac{c}{\Delta\nu_{\mathrm{Cs}}},
--   $$
--
--   $$
--   1\ \mathrm{kg} = \frac{8.987\,551\,787\,368\,1764\times10^{40}}{6.091\,102\,297\,113\,866\,55}\,
--   \frac{h\,\Delta\nu_{\mathrm{Cs}}}{c^{2}},\qquad
--   1\ \mathrm A = \frac{10^{9}}{1.472\,821\,982\,686\,006\,218}\,e\,\Delta\nu_{\mathrm{Cs}},
--   $$
--
--   $$
--   1\ \mathrm K = \frac{13.806\,49}{6.091\,102\,297\,113\,866\,55}\,
--   \frac{h\,\Delta\nu_{\mathrm{Cs}}}{k},\qquad
--   1\ \mathrm{mol} = \frac{6.022\,140\,76\times10^{23}}{N_{\mathrm A}},
--   $$
--
--   $$
--   1\ \mathrm{cd} = \frac{10^{11}}{3.824\,339\,691\,519\,516\,481\,631\,301\,046\,05}\,
--   h\,\Delta\nu_{\mathrm{Cs}}^{2}\,K_{\mathrm{cd}}.
--   $$
--
--   Since each unit on the left has numerical value $1$ in the SI, the assertion is that each of the
--   seven expressions on the right evaluates to exactly $1$. Six of the seven involve
--   $\Delta\nu_{\mathrm{Cs}}$; the mole does not.
--
--   The theorem is the arithmetic core of the 2019 SI: it certifies that the published coefficients
--   of the base units are consistent with the fixed values of the defining constants.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Summary'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem si_base_units_from_defining_constants :
    9192631770 / dnuCs = 1
    ∧ (9192631770 / 299792458) * (cLight / dnuCs) = 1
    ∧ (8.9875517873681764e40 / 6.09110229711386655) * (hPlanck * dnuCs / cLight ^ 2) = 1
    ∧ (1e9 / 1.472821982686006218) * (eCharge * dnuCs) = 1
    ∧ (13.80649 / 6.09110229711386655) * (hPlanck * dnuCs / kBoltzmann) = 1
    ∧ 6.02214076e23 / nAvogadro = 1
    ∧ (1e11 / 3.82433969151951648163130104605) * (hPlanck * dnuCs ^ 2 * kcdLumEff) = 1 := by sorry

end CaesiumStandard
