-- Prove2me | Theorems.Thm_ActuarialValuation_pucRetirementFactor_nonneg
-- name    : ActuarialValuation.pucRetirementFactor_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:16:05.116984+00:00
-- url     : https://prove2.me/theorems/db21542a-6b33-4f5f-9bfd-0c1f02956723
-- title:
--   Actuarial liability and normal cost: pucRetirementFactor_nonneg
-- statement:
--   The monetary actuarial unit cost is nonnegative with positive survival, discount and pension annuity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p,v,a\ge0\Rightarrow f\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucRetirementFactor

namespace ActuarialValuation

theorem pucRetirementFactor_nonneg (p v ann : ℝ) (hp : 0 ≤ p) (hv : 0 ≤ v) (ha : 0 ≤ ann) : 0 ≤ pucRetirementFactor p v ann := by sorry

end ActuarialValuation
