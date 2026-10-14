-- Prove2me | Theorems.Thm_ActuarialValuation_ruCumulativeMargin_eq_surplus
-- name    : ActuarialValuation.ruCumulativeMargin_eq_surplus
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:01:06.801467+00:00
-- url     : https://prove2.me/theorems/95382b92-368d-413c-895e-4d20526162eb
-- title:
--   First passage and deficit at ruin: ruCumulativeMargin_eq_surplus
-- statement:
--   Independent premium/claim accounting agrees with the period-end surplus calculation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_n=U_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruCumulativeMargin

namespace ActuarialValuation

theorem ruCumulativeMargin_eq_surplus (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruCumulativeMargin u c x n = ruPathSurplus u c x n := by sorry

end ActuarialValuation
