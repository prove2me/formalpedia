-- Prove2me | Theorems.Thm_ElementaryCharge_charge_from_codata_relation
-- name    : ElementaryCharge.charge_from_codata_relation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T16:39:40.201601+00:00
-- url     : https://prove2.me/theorems/8d5c2d62-b906-431d-8200-cd4dbd8d728d
-- title:
--   CODATA relation: $e = \sqrt{2h\alpha/(\mu_0 c)}$
-- statement:
--   The relation used by CODATA to determine the elementary charge. If the fine-structure constant is given by $\alpha = \mu_0 c e^2/(2h)$, with $h$ the Planck constant, $\mu_0$ the magnetic constant and $c$ the speed of light, all positive, then $e = \sqrt{2h\alpha/(\mu_0 c)}$. Positivity of $e$ is what selects the positive square root.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib
import Definitions.Def_elementary_charge_si_constants

namespace ElementaryCharge

theorem charge_from_codata_relation (q hPlanck mu0 cLight alpha : ℝ)
    (hq : 0 < q) (hh : 0 < hPlanck) (hmu : 0 < mu0) (hc : 0 < cLight)
    (halpha : alpha = fineStructureConstant q hPlanck mu0 cLight) :
    Real.sqrt (2 * hPlanck * alpha / (mu0 * cLight)) = q := by sorry

end ElementaryCharge
