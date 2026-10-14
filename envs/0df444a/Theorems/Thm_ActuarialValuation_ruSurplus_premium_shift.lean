-- Prove2me | Theorems.Thm_ActuarialValuation_ruSurplus_premium_shift
-- name    : ActuarialValuation.ruSurplus_premium_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:56:07.866028+00:00
-- url     : https://prove2.me/theorems/a12eaf33-3483-49fc-bf88-d4bceb3c7ae8
-- title:
--   Premium and claim surplus cash-flow recursion: ruSurplus_premium_shift
-- statement:
--   Changing the premium rate affects future surplus in proportion to the elapsed periods. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_n(c+δ)=U_n(c)+nδ
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus

namespace ActuarialValuation

theorem ruSurplus_premium_shift (u c δ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruPathSurplus u (c+δ) x n = ruPathSurplus u c x n + (n:ℝ)*δ := by sorry

end ActuarialValuation
