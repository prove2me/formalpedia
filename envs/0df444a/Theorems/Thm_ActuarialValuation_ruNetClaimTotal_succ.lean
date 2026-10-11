-- Prove2me | Theorems.Thm_ActuarialValuation_ruNetClaimTotal_succ
-- name    : ActuarialValuation.ruNetClaimTotal_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:56:50.678616+00:00
-- url     : https://prove2.me/theorems/425e275d-442a-4871-8158-c47c5bb2d9cd
-- title:
--   Premium and claim surplus cash-flow recursion: ruNetClaimTotal_succ
-- statement:
--   Accumulated net loss includes each period's claim less premium. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   L_{n+1}=L_n+X_n-c
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruNetClaim
import Definitions.Def_actuarial_ruNetClaimTotal

namespace ActuarialValuation

theorem ruNetClaimTotal_succ (x : ℕ → ℝ) (c : ℝ) (n : ℕ) : ruNetClaimTotal x c (n+1) = ruNetClaimTotal x c n + ruNetClaim (x n) c := by sorry

end ActuarialValuation
