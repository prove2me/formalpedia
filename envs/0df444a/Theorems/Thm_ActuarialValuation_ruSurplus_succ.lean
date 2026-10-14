-- Prove2me | Theorems.Thm_ActuarialValuation_ruSurplus_succ
-- name    : ActuarialValuation.ruSurplus_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:34.074986+00:00
-- url     : https://prove2.me/theorems/3f76c1ba-a790-4513-85dc-a91930424cd9
-- title:
--   Premium and claim surplus cash-flow recursion: ruSurplus_succ
-- statement:
--   Cramér-Lundberg style discrete surplus rises by premium and falls by the new claim. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_{n+1}=U_n+c-X_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 433. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Palmowski, Ramsden and Papaioannou (2018), Parisian ruin for the dual risk process in discrete-time, https://link.springer.com/article/10.1007/s13385-018-0172-8. Parent topic: Actuarial surplus and ruin: first-passage event, claim timing, nonnegative deficit, retained loss and reinsurance comparison for finite portfolios. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus

namespace ActuarialValuation

theorem ruSurplus_succ (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ruPathSurplus u c x (n+1) = ruPathSurplus u c x n + c - x n := by sorry

end ActuarialValuation
