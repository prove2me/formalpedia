-- Prove2me | Theorems.Thm_ActuarialValuation_ruReinsurance_split
-- name    : ActuarialValuation.ruReinsurance_split
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:02:37.481716+00:00
-- url     : https://prove2.me/theorems/1e611014-32d3-4165-b2e9-f2ff11178bca
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruReinsurance_split
-- statement:
--   Every individual claim partitions without overlap between retention and excess-of-loss reimbursement. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   X=X^R+Y
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruStopLoss
import Definitions.Def_actuarial_ruRetained

namespace ActuarialValuation

theorem ruReinsurance_split (x d : ℝ) : ruRetained x d + ruStopLoss x d = x := by sorry

end ActuarialValuation
