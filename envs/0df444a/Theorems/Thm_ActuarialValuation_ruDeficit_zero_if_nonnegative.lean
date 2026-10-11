-- Prove2me | Theorems.Thm_ActuarialValuation_ruDeficit_zero_if_nonnegative
-- name    : ActuarialValuation.ruDeficit_zero_if_nonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:00:44.643995+00:00
-- url     : https://prove2.me/theorems/6e6b4b7a-89f4-4278-ad28-4ef1d600776f
-- title:
--   First passage and deficit at ruin: ruDeficit_zero_if_nonnegative
-- statement:
--   Solvency at the observation boundary implies no shortfall. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_n≥0⇒D_n=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruDeficit

namespace ActuarialValuation

theorem ruDeficit_zero_if_nonnegative (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) (h : 0 ≤ ruPathSurplus u c x n) : ruDeficit u c x n = 0 := by sorry

end ActuarialValuation
