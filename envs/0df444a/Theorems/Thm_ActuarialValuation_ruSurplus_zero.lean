-- Prove2me | Theorems.Thm_ActuarialValuation_ruSurplus_zero
-- name    : ActuarialValuation.ruSurplus_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:20.817974+00:00
-- url     : https://prove2.me/theorems/7c47fe2b-3975-4975-8f11-88f1df6d6ea7
-- title:
--   Premium and claim surplus cash-flow recursion: ruSurplus_zero
-- statement:
--   The insurer enters the model with initial capital u. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_0=u
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus

namespace ActuarialValuation

theorem ruSurplus_zero (u c : ℝ) (x : ℕ → ℝ) : ruPathSurplus u c x 0 = u := by sorry

end ActuarialValuation
