-- Prove2me | Theorems.Thm_ActuarialValuation_ruFirstRuin_by
-- name    : ActuarialValuation.ruFirstRuin_by
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:59:08.126846+00:00
-- url     : https://prove2.me/theorems/24ce6574-20a1-4787-9158-39e56fb8e0f3
-- title:
--   First passage and deficit at ruin: ruFirstRuin_by
-- statement:
--   The first ruin period must be contained in the event of ruin by that period. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   τ=n implies R_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinBy
import Definitions.Def_actuarial_ruFirstRuin

namespace ActuarialValuation

theorem ruFirstRuin_by (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) (h : ruFirstRuin u c x n) : ruRuinBy u c x n := by sorry

end ActuarialValuation
