-- Prove2me | Theorems.Thm_ActuarialValuation_ruRetainedSurplus_reconcile
-- name    : ActuarialValuation.ruRetainedSurplus_reconcile
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:03:20.428348+00:00
-- url     : https://prove2.me/theorems/82498719-a234-4284-9ac6-45fc64e22464
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruRetainedSurplus_reconcile
-- statement:
--   Holding premium fixed, reinsurance increases surplus exactly by cumulative recovered claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U^R_n=U_n+Y_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruRetainedSurplus
import Definitions.Def_actuarial_ruCededTotal

namespace ActuarialValuation

theorem ruRetainedSurplus_reconcile (u c d : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruRetainedSurplus u c d x n = ruPathSurplus u c x n + ruCededTotal x d n := by sorry

end ActuarialValuation
