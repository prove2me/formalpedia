-- Prove2me | Theorems.Thm_ActuarialValuation_pucAccruedBenefit_add
-- name    : ActuarialValuation.pucAccruedBenefit_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:07:49.23018+00:00
-- url     : https://prove2.me/theorems/e76169a2-045b-44b7-af30-7331416230f2
-- title:
--   Projected service and accrued benefits: pucAccruedBenefit_add
-- statement:
--   Service credited under two benefit streams is additive. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B(u+v)=B(u)+B(v)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit

namespace ActuarialValuation

theorem pucAccruedBenefit_add (u v : ℕ → ℝ) (n : ℕ) : pucAccruedBenefit (fun t => u t + v t) n = pucAccruedBenefit u n + pucAccruedBenefit v n := by sorry

end ActuarialValuation
