-- Prove2me | Theorems.Thm_ElementaryCharge_elementary_charge_determinations_agree
-- name    : ElementaryCharge.elementary_charge_determinations_agree
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:49:51.058801+00:00
-- url     : https://prove2.me/theorems/90081def-d0a8-4ae1-a0fa-594bd818064d
-- title:
--   The three determinations of $e$ agree with the exact SI value
-- statement:
--   The goal of the mission: the three routes to the elementary charge recorded in the source all return the same number, the exact 2019 SI value $e = 1.602176634\times10^{-19}$ C. Concretely, at the SI fixed values of $N_\mathrm{A}$, $h$ and $c$, and for any positive magnetic constant $\mu_0$ with $\alpha = \mu_0 c e^2/(2h)$: the Faraday constant has the exact value $96\,485.3321233100184\ \mathrm{C\,mol^{-1}}$; the electrolysis route gives $F/N_\mathrm{A} = e$; the quantum-electrical route gives $2/(K_\mathrm{J}R_\mathrm{K}) = e$; and the CODATA route gives $\sqrt{2h\alpha/(\mu_0 c)} = e$.
-- source:
--   "Elementary charge", Wikipedia, https://en.wikipedia.org/wiki/Elementary_charge (uploaded PDF revision). Sections: "As a unit"; "Quantization"; "Lack of fractional charges"; "In terms of the Avogadro constant and Faraday constant"; "From the Josephson and von Klitzing constants"; "CODATA method".

import Mathlib
import Definitions.Def_elementary_charge_si_constants

namespace ElementaryCharge

theorem elementary_charge_determinations_agree (mu0 alpha : ℝ) (hmu : 0 < mu0)
    (halpha : alpha = fineStructureConstant eSI planckSI mu0 lightSpeedSI) :
    faradayConstant avogadroSI eSI = 964853321233100184 / 10 ^ 13 ∧
    faradayConstant avogadroSI eSI / avogadroSI = eSI ∧
    2 / (josephsonConstant eSI planckSI * vonKlitzingConstant eSI planckSI)
      = eSI ∧
    Real.sqrt (2 * planckSI * alpha / (mu0 * lightSpeedSI)) = eSI := by sorry

end ElementaryCharge
