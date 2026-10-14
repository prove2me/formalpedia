-- Prove2me | Theorems.Thm_ActuarialValuation_ruRuinAt_characterise
-- name    : ActuarialValuation.ruRuinAt_characterise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:57:25.508304+00:00
-- url     : https://prove2.me/theorems/f979e162-3cc7-4fa0-8346-90ef2da9f2bc
-- title:
--   First passage and deficit at ruin: ruRuinAt_characterise
-- statement:
--   Period n is ruined exactly when cumulative claim outgo exceeds available capital plus cumulative premium. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   ruin iff C_n>u+P_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruClaimTotal
import Definitions.Def_actuarial_ruPremiumTotal
import Definitions.Def_actuarial_ruRuinAt

namespace ActuarialValuation

theorem ruRuinAt_characterise (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruRuinAt u c x n ↔ ruClaimTotal x n > u+ruPremiumTotal c n := by sorry

end ActuarialValuation
