-- Prove2me | Theorems.Thm_ActuarialValuation_ruPremiumTotal_succ
-- name    : ActuarialValuation.ruPremiumTotal_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:54:52.354749+00:00
-- url     : https://prove2.me/theorems/21924398-a202-4ce0-bd16-7e10df1e0785
-- title:
--   Premium and claim surplus cash-flow recursion: ruPremiumTotal_succ
-- statement:
--   Total premium receipts follow exact one-step accumulation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_{n+1}=P_n+c
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPremiumTotal

namespace ActuarialValuation

theorem ruPremiumTotal_succ (rate : ℝ) (n : ℕ) : ruPremiumTotal rate (n+1) = ruPremiumTotal rate n + rate := by sorry

end ActuarialValuation
