-- Prove2me | Theorems.Thm_ActuarialValuation_ruDeficit_positive_if_ruin
-- name    : ActuarialValuation.ruDeficit_positive_if_ruin
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:00:27.300117+00:00
-- url     : https://prove2.me/theorems/63af3fab-98fb-458f-bd01-5199c8320fc5
-- title:
--   First passage and deficit at ruin: ruDeficit_positive_if_ruin
-- statement:
--   Actual ruin implies a strictly positive monetary deficit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_n<0⇒D_n>0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruDeficit

namespace ActuarialValuation

theorem ruDeficit_positive_if_ruin (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) (h : ruRuinAt u c x n) : 0 < ruDeficit u c x n := by sorry

end ActuarialValuation
