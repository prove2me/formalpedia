-- Prove2me | Theorems.Thm_ElementaryCharge_charge_from_faraday_avogadro
-- name    : ElementaryCharge.charge_from_faraday_avogadro
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T16:21:27.016258+00:00
-- url     : https://prove2.me/theorems/ff224827-72de-4978-b9b0-23fc29ce98c6
-- title:
--   Electrolysis route: $e = F/N_\mathrm{A}$
-- statement:
--   The charge of one mole of electrons, divided by the number of electrons in a mole, is the charge of a single electron: for any nonzero $N_\mathrm{A}$ and any $q$, $(N_\mathrm{A}q)/N_\mathrm{A} = q$. This is the relation $e = F/N_\mathrm{A}$ on which the first determinations of the elementary charge, from Faraday's laws of electrolysis, were based. The hypothesis $N_\mathrm{A}\neq 0$ is required because division by zero returns $0$ in Lean.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib
import Definitions.Def_elementary_charge_si_constants

namespace ElementaryCharge

theorem charge_from_faraday_avogadro (NA q : ℝ) (hNA : NA ≠ 0) :
    faradayConstant NA q / NA = q := by sorry

end ElementaryCharge
