-- Prove2me | Theorems.Thm_ActuarialValuation_ruNetClaimTotal_reconcile
-- name    : ActuarialValuation.ruNetClaimTotal_reconcile
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:57:04.406418+00:00
-- url     : https://prove2.me/theorems/05782138-6b4a-4a6f-acab-afc9d1464c5a
-- title:
--   Premium and claim surplus cash-flow recursion: ruNetClaimTotal_reconcile
-- statement:
--   Surplus is opening capital minus cumulative net claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_n=u-Σ(X-c)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruNetClaimTotal

namespace ActuarialValuation

theorem ruNetClaimTotal_reconcile (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruPathSurplus u c x n = u - ruNetClaimTotal x c n := by sorry

end ActuarialValuation
