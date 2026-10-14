-- Prove2me | Theorems.Thm_ActuarialValuation_ruDeficit_if_ruin
-- name    : ActuarialValuation.ruDeficit_if_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:00:09.382801+00:00
-- url     : https://prove2.me/theorems/7c0b96c7-47a1-4511-abd9-685febf2017c
-- title:
--   First passage and deficit at ruin: ruDeficit_if_ruin
-- statement:
--   At negative surplus the exact shortfall equals the magnitude of the uncovered liability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_n<0⇒D_n=-U_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruDeficit

namespace ActuarialValuation

theorem ruDeficit_if_ruin (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) (h : ruRuinAt u c x n) : ruDeficit u c x n = -ruPathSurplus u c x n := by sorry

end ActuarialValuation
