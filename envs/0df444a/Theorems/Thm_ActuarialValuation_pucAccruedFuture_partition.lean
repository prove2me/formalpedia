-- Prove2me | Theorems.Thm_ActuarialValuation_pucAccruedFuture_partition
-- name    : ActuarialValuation.pucAccruedFuture_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:12:33.935978+00:00
-- url     : https://prove2.me/theorems/42fab839-23aa-46ef-8810-43de7f3af8e5
-- title:
--   Projected service and accrued benefits: pucAccruedFuture_partition
-- statement:
--   Past and future projected service partition full service accrual without overlap. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B_{n+m}=B_n+F_{n,m}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit
import Definitions.Def_actuarial_pucTotalBenefit

namespace ActuarialValuation

theorem pucAccruedFuture_partition (u : ℕ → ℝ) (n m : ℕ) : pucTotalBenefit u n m = pucAccruedBenefit u (n+m) := by sorry

end ActuarialValuation
