-- Prove2me | Theorems.Thm_ActuarialValuation_pucFundingSurplus_zero
-- name    : ActuarialValuation.pucFundingSurplus_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:14:38.417144+00:00
-- url     : https://prove2.me/theorems/1ff62f80-5d84-49f0-9ad9-dc505550e752
-- title:
--   Funding shortfall and contribution amortisation: pucFundingSurplus_zero
-- statement:
--   With no amortisation contribution, funding surplus is assets less liability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S(0)=A-AL
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucFundingSurplus

namespace ActuarialValuation

theorem pucFundingSurplus_zero (a al : ℝ) : pucFundingSurplus a 0 1 al = a - al := by sorry

end ActuarialValuation
