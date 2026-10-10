-- Prove2me | Theorems.Thm_ActuarialValuation_pucActuarialLiability_nonneg
-- name    : ActuarialValuation.pucActuarialLiability_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:17:28.463138+00:00
-- url     : https://prove2.me/theorems/73f4b7f1-56e4-4320-bc22-4252a224c2b1
-- title:
--   Actuarial liability and normal cost: pucActuarialLiability_nonneg
-- statement:
--   A nonnegative annual pension and annuity factor yield a nonnegative actuarial accrued liability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B_n,f\ge0\Rightarrow AL_n\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit
import Definitions.Def_actuarial_pucActuarialLiability

namespace ActuarialValuation

theorem pucActuarialLiability_nonneg (u : ℕ → ℝ) (n : ℕ) (f : ℝ) (hu : 0 ≤ pucAccruedBenefit u n) (hf : 0 ≤ f) : 0 ≤ pucActuarialLiability u n f := by sorry

end ActuarialValuation
