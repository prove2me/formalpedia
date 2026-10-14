-- Prove2me | Theorems.Thm_ActuarialValuation_ruSurplus_claim_shift
-- name    : ActuarialValuation.ruSurplus_claim_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:56:21.573122+00:00
-- url     : https://prove2.me/theorems/f031d269-0595-47fc-9303-83538e1f1d50
-- title:
--   Premium and claim surplus cash-flow recursion: ruSurplus_claim_shift
-- statement:
--   Adding a claim stream reduces surplus by its actual aggregate claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_n(x+y)=U_n(x)-C_n(y)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruClaimTotal
import Definitions.Def_actuarial_ruPathSurplus

namespace ActuarialValuation

theorem ruSurplus_claim_shift (u c : ℝ) (x y : ℕ → ℝ) (n : ℕ) : ruPathSurplus u c (fun k => x k+y k) n = ruPathSurplus u c x n - ruClaimTotal y n := by sorry

end ActuarialValuation
