-- Prove2me | Theorems.Thm_DerivativeChainContinuation_last_derivative_strict_midpoint
-- name    : DerivativeChainContinuation.last_derivative_strict_midpoint
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:37:51.127934+00:00
-- url     : https://prove2.me/theorems/ef024c88-a88c-4d7f-920a-6ebe0f3e97c2
-- title:
--   The largest derivative root lies beyond the last midpoint
-- statement:
--   Let d≥3. Let a_0≤⋯≤a_(d-1) and b_0≤⋯≤b_(d-2) be real tuples satisfying a_i≤b_i≤a_(i+1), and (∏_(i=0)^(d-1)(X-a_i))′=d∏_(i=0)^(d-2)(X-b_i). Repeated values are allowed. If a_(d-2)<a_(d-1), then (a_(d-2)+a_(d-1))/2<b_(d-2).
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyReal.lean, lines 39-94, SHA-256 186feed2d495e8a1a66a0ecd5c2a2fbad651f03f45bd1d7f1a175d09e35fe59e.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.last_derivative_strict_midpoint (n : ℕ) (a : Fin (n+3) → ℝ)
    (b : Fin (n+2) → ℝ) (ha : Monotone a) (hb : Monotone b)
    (hinter : ∀ i : Fin (n+2), a i.castSucc ≤ b i ∧ b i ≤ a i.succ)
    (hder : (realRootProduct a).derivative = C (n+3 : ℝ)*realRootProduct b)
    (hgap : a (Fin.last (n+1)).castSucc < a (Fin.last (n+2))) :
    (a (Fin.last (n+1)).castSucc+a (Fin.last (n+2)))/2 <
      b (Fin.last (n+1)) := by sorry
