-- Prove2me | Theorems.Thm_ActuarialValuation_ruRuinBy_mono
-- name    : ActuarialValuation.ruRuinBy_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:58:22.207438+00:00
-- url     : https://prove2.me/theorems/5fad8ab9-0a5a-42c4-a768-a88cd86b741f
-- title:
--   First passage and deficit at ruin: ruRuinBy_mono
-- statement:
--   Ruin occurrence is monotone in the time horizon, even if capital later recovers. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_n⊆R_m
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinBy

namespace ActuarialValuation

theorem ruRuinBy_mono (u c : ℝ) (x : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) (hr : ruRuinBy u c x n) : ruRuinBy u c x m := by sorry

end ActuarialValuation
