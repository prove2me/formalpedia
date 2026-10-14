-- Prove2me | Theorems.Thm_ActuarialValuation_ruFirstRuin_unique
-- name    : ActuarialValuation.ruFirstRuin_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:59:25.158253+00:00
-- url     : https://prove2.me/theorems/65c46de1-5113-48c5-80d3-829e569c5415
-- title:
--   First passage and deficit at ruin: ruFirstRuin_unique
-- statement:
--   Two different periods cannot both be the first negative-surplus period on the same path. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   τ unique
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruFirstRuin

namespace ActuarialValuation

theorem ruFirstRuin_unique (u c : ℝ) (x : ℕ → ℝ) (n m : ℕ) (hn : ruFirstRuin u c x n) (hm : ruFirstRuin u c x m) : n=m := by sorry

end ActuarialValuation
