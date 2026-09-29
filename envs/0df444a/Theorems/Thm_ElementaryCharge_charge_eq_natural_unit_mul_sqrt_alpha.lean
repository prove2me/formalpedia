-- Prove2me | Theorems.Thm_ElementaryCharge_charge_eq_natural_unit_mul_sqrt_alpha
-- name    : ElementaryCharge.charge_eq_natural_unit_mul_sqrt_alpha
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T16:40:56.348984+00:00
-- url     : https://prove2.me/theorems/100b9698-8780-42b4-8f87-e66cb50cb41e
-- title:
--   Natural units: $e = \sqrt{4\pi\varepsilon_0\hbar c}\,\sqrt{\alpha}$
-- statement:
--   In natural unit systems whose unit of charge is $q_0 = \sqrt{4\pi\varepsilon_0\hbar c}$, the elementary charge is $e = q_0\sqrt{\alpha}$, where $\alpha = e^2/(4\pi\varepsilon_0\hbar c)$ is the fine-structure constant, $\varepsilon_0$ the electric constant, $\hbar$ the reduced Planck constant and $c$ the speed of light. The hypothesis $4\pi\varepsilon_0\hbar c > 0$ keeps both square roots away from Lean's junk value on negative arguments.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib
import Definitions.Def_elementary_charge_si_constants

namespace ElementaryCharge

theorem charge_eq_natural_unit_mul_sqrt_alpha (q eps0 hbar cLight alpha : ℝ)
    (hq : 0 < q) (hpos : 0 < 4 * Real.pi * eps0 * hbar * cLight)
    (halpha : alpha = q ^ 2 / (4 * Real.pi * eps0 * hbar * cLight)) :
    naturalUnitCharge eps0 hbar cLight * Real.sqrt alpha = q := by sorry

end ElementaryCharge
