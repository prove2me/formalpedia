-- Prove2me | Theorems.Thm_ActuarialValuation_ruPremiumTotal_add_rates
-- name    : ActuarialValuation.ruPremiumTotal_add_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:02.696993+00:00
-- url     : https://prove2.me/theorems/976a1b57-12f4-473f-9919-ebcd98ad8e1c
-- title:
--   Premium and claim surplus cash-flow recursion: ruPremiumTotal_add_rates
-- statement:
--   Separate premium sources can be combined under one payment schedule. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_{a+b}=P_a+P_b
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPremiumTotal

namespace ActuarialValuation

theorem ruPremiumTotal_add_rates (a b : ℝ) (n : ℕ) : ruPremiumTotal (a+b) n = ruPremiumTotal a n + ruPremiumTotal b n := by sorry

end ActuarialValuation
