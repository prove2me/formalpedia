-- Prove2me | Theorems.Thm_ActuarialValuation_ruRuinBy_succ
-- name    : ActuarialValuation.ruRuinBy_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:58:02.756985+00:00
-- url     : https://prove2.me/theorems/31ce00fa-83c8-4ecc-9fcf-003be24aaa89
-- title:
--   First passage and deficit at ruin: ruRuinBy_succ
-- statement:
--   The finite-horizon first-passage event evolves by adding the new observation boundary. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_{n+1}=R_n ∨ A_{n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruRuinBy

namespace ActuarialValuation

theorem ruRuinBy_succ (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruRuinBy u c x (n+1) ↔ ruRuinBy u c x n ∨ ruRuinAt u c x (n+1) := by sorry

end ActuarialValuation
