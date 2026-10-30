-- Prove2me | Theorems.Thm_DerivativeChainContinuation_real_greedy_min_cost
-- name    : DerivativeChainContinuation.real_greedy_min_cost
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:03:31.071794+00:00
-- url     : https://prove2.me/theorems/daa89204-7195-4d54-bdea-07767ce5e93d
-- title:
--   The least greedy cost on a real source is attained exactly
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. For real source roots let u=(Σ_j a_j)/N, A=min_j a_j, and B=max_j a_j, with multiplicities retained. For n≥1 there exists an actual greedy history z with L(z)=min(u-A,B-u), with L(z)≤L(w) for every actual greedy history w, and with L(z)≤(B-A)/2. This minimum ranges only over histories allowed by the local nearest-parent rule.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyStatement.lean, lines 78-130, SHA-256 b0b4225b71610ef2d6a2e072dc060bf94cb556fe8b6c938713302f20f8d9fac9.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.real_greedy_min_cost (n : ℕ) (hn : 1≤n) (a : Fin (n+1) → ℝ) :
    ∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
      chainCost z=min (realCentroid a-orderedSource a 0)
        (orderedSource a (Fin.last n)-realCentroid a) ∧
      (∀ w : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) w →
        chainCost z≤chainCost w) ∧
      chainCost z≤(orderedSource a (Fin.last n)-orderedSource a 0)/2 := by sorry
