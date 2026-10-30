-- Prove2me | Theorems.Thm_DerivativeChainContinuation_first_derivative_unique_nearest
-- name    : DerivativeChainContinuation.first_derivative_unique_nearest
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:42:00.483095+00:00
-- url     : https://prove2.me/theorems/ede60c8c-0036-4f58-9b39-2ef62ceae6e7
-- title:
--   The smallest derivative root has a unique nearest parent location
-- statement:
--   Let d≥3. Let a_0≤⋯≤a_(d-1) and b_0≤⋯≤b_(d-2) be real tuples satisfying a_i≤b_i≤a_(i+1), and (∏_(i=0)^(d-1)(X-a_i))′=d∏_(i=0)^(d-2)(X-b_i). Repeated values are allowed. For every parent slot i with a_i≠a_0, |a_0-b_0|<|a_i-b_0|. Thus the smallest parent value is the unique nearest root location to the smallest child value.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyReal.lean, lines 150-171, SHA-256 186feed2d495e8a1a66a0ecd5c2a2fbad651f03f45bd1d7f1a175d09e35fe59e.

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

theorem DerivativeChainContinuation.first_derivative_unique_nearest (n : ℕ) (a : Fin (n+3) → ℝ)
    (b : Fin (n+2) → ℝ) (ha : Monotone a) (hb : Monotone b)
    (hinter : ∀ i : Fin (n+2), a i.castSucc ≤ b i ∧ b i ≤ a i.succ)
    (hder : (realRootProduct a).derivative = C (n+3 : ℝ)*realRootProduct b)
    (i : Fin (n+3)) (hi : a i ≠ a 0) :
    |a 0-b 0| < |a i-b 0| := by sorry
