-- Prove2me | Theorems.Thm_CaesiumStandard_electromagnetic_units_from_caesium_parameters
-- name    : CaesiumStandard.electromagnetic_units_from_caesium_parameters
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:33:20.242414+00:00
-- url     : https://prove2.me/theorems/35992a1e-a890-4cd5-a72c-e6a160bf470c
-- title:
--   Coulomb, volt, ohm, siemens, farad, weber, henry and tesla
-- statement:
--   **Coulomb, volt, ohm, siemens, farad, weber, henry and tesla.**
--
--   From the fixed value of the elementary charge and the caesium radiation parameters, the
--   *Electromagnetic units* section of the source gives the exact relations
--
--   $$1\ \mathrm C = \frac{10^{19}}{1.602\,176\,634}\,e,\qquad
--   1\ \mathrm V = \frac{1.602\,176\,634\times10^{5}}{6.091\,102\,297\,113\,866\,55}\,
--   \frac{\Delta E_{\mathrm{Cs}}}{e},$$
--
--   $$1\ \Omega = \frac{2.359\,720\,966\,701\,071\,721\,258\,310\,212\times10^{-4}}
--   {6.091\,102\,297\,113\,866\,55}\,\frac{h}{e^{2}},\qquad
--   1\ \mathrm S = \frac{6.091\,102\,297\,113\,866\,55\times10^{4}}
--   {2.359\,720\,966\,701\,071\,721\,258\,310\,212}\,\frac{e^{2}}{h},$$
--
--   $$1\ \mathrm F = \frac{6.091\,102\,297\,113\,866\,55\times10^{14}}{2.566\,969\,966\,535\,569\,956}\,
--   \frac{e^{2}}{\Delta E_{\mathrm{Cs}}},\qquad
--   1\ \mathrm{Wb} = \frac{1.602\,176\,634\times10^{15}}{6.626\,070\,15}\,\frac{h}{e},$$
--
--   $$1\ \mathrm H = \frac{2.359\,720\,966\,701\,071\,721\,258\,310\,212\times10^{6}}{6.626\,070\,15}\,
--   \frac{h\,\Delta t_{\mathrm{Cs}}}{e^{2}},\qquad
--   1\ \mathrm T = \frac{1.439\,964\,547\,058\,622\,858\,327\,023\,76\times10^{12}}
--   {5.599\,326\,049\,076\,890\,895\,507\,029\,35}\,
--   \frac{\Delta E_{\mathrm{Cs}}\,\Delta t_{\mathrm{Cs}}}{e\,\Delta\lambda_{\mathrm{Cs}}^{2}} .$$
--
--   Each of the eight displayed expressions is asserted to have numerical value exactly $1$. The ohm
--   relation expresses the SI ohm as an exact rational multiple of the von Klitzing constant $h/e^{2}$,
--   and the siemens relation is its reciprocal form.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Electromagnetic units'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem electromagnetic_units_from_caesium_parameters :
    (1e19 / 1.602176634) * eCharge = 1
    ∧ (1.602176634e5 / 6.09110229711386655) * (ECs / eCharge) = 1
    ∧ (2.359720966701071721258310212e-4 / 6.09110229711386655) * (hPlanck / eCharge ^ 2) = 1
    ∧ (6.09110229711386655e4 / 2.359720966701071721258310212) * (eCharge ^ 2 / hPlanck) = 1
    ∧ (6.09110229711386655e14 / 2.566969966535569956) * (eCharge ^ 2 / ECs) = 1
    ∧ (1.602176634e15 / 6.62607015) * (hPlanck / eCharge) = 1
    ∧ (2.359720966701071721258310212e6 / 6.62607015) * (hPlanck * tCs / eCharge ^ 2) = 1
    ∧ (1.43996454705862285832702376e12 / 5.59932604907689089550702935)
        * (ECs * tCs / (eCharge * lambdaCs ^ 2)) = 1 := by sorry

end CaesiumStandard
