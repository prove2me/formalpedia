-- Prove2me | Theorems.Thm_ActuarialValuation_pucAmortisationRate_cancel
-- name    : ActuarialValuation.pucAmortisationRate_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:11:16.135191+00:00
-- url     : https://prove2.me/theorems/1967120c-9261-4644-8fe6-2730d4a59b38
-- title:
--   Funding shortfall and contribution amortisation: pucAmortisationRate_cancel
-- statement:
--   The amortisation contribution value exactly extinguishes the valuation-date funding deficit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c^*F=UL
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAmortisationRate

namespace ActuarialValuation

theorem pucAmortisationRate_cancel (u base : ℝ) (hb : base ≠ 0) : pucAmortisationRate u base * base = u := by sorry

end ActuarialValuation
