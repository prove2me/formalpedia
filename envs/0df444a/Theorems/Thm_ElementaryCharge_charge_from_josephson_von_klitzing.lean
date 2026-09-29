-- Prove2me | Theorems.Thm_ElementaryCharge_charge_from_josephson_von_klitzing
-- name    : ElementaryCharge.charge_from_josephson_von_klitzing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T16:39:18.184695+00:00
-- url     : https://prove2.me/theorems/d83a2070-55ae-4b7f-9009-008ddb7bf1ff
-- title:
--   Quantum-electrical route: $e = 2/(K_\mathrm{J}R_\mathrm{K})$
-- statement:
--   The Josephson constant $K_\mathrm{J} = 2e/h$ is measurable through the Josephson effect and the von Klitzing constant $R_\mathrm{K} = h/e^2$ through the quantum Hall effect. From the two together the elementary charge is recovered as $e = 2/(K_\mathrm{J}R_\mathrm{K})$, for any nonzero charge $e$ and nonzero Planck constant $h$; the Planck constant cancels.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib
import Definitions.Def_elementary_charge_si_constants

namespace ElementaryCharge

theorem charge_from_josephson_von_klitzing (q hPlanck : ℝ) (hq : q ≠ 0)
    (hh : hPlanck ≠ 0) :
    2 / (josephsonConstant q hPlanck * vonKlitzingConstant q hPlanck) = q := by sorry

end ElementaryCharge
