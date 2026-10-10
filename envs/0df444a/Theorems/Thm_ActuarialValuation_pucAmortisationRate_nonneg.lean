-- Prove2me | Theorems.Thm_ActuarialValuation_pucAmortisationRate_nonneg
-- name    : ActuarialValuation.pucAmortisationRate_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:11:05.540665+00:00
-- url     : https://prove2.me/theorems/850eeaf1-19dc-4aa1-9d24-778ce90475c3
-- title:
--   Funding shortfall and contribution amortisation: pucAmortisationRate_nonneg
-- statement:
--   Positive payroll PV permits nonnegative amortisation of positive funding deficit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   UL\ge0,F>0\Rightarrow c^*\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAmortisationRate

namespace ActuarialValuation

theorem pucAmortisationRate_nonneg (u base : ℝ) (hu : 0 ≤ u) (hb : 0 < base) : 0 ≤ pucAmortisationRate u base := by sorry

end ActuarialValuation
