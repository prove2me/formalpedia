-- Prove2me | Theorems.Thm_ActuarialValuation_ruRetainedSurplus_ge_gross
-- name    : ActuarialValuation.ruRetainedSurplus_ge_gross
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:03:37.512893+00:00
-- url     : https://prove2.me/theorems/d55a74fd-df91-4901-b8e3-90346c54bf6d
-- title:
--   Stop-loss reinsurance, retained deficit and pathwise capital: ruRetainedSurplus_ge_gross
-- statement:
--   Stop-loss reimbursements improve or preserve pathwise capital when their cost is ignored by assumption. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U^R_n≥U_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruRetainedSurplus

namespace ActuarialValuation

theorem ruRetainedSurplus_ge_gross (u c d : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruPathSurplus u c x n ≤ ruRetainedSurplus u c d x n := by sorry

end ActuarialValuation
