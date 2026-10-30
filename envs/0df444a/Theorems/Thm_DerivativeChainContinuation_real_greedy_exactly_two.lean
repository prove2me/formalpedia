-- Prove2me | Theorems.Thm_DerivativeChainContinuation_real_greedy_exactly_two
-- name    : DerivativeChainContinuation.real_greedy_exactly_two
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:59:05.304017+00:00
-- url     : https://prove2.me/theorems/2e4a7a03-75b8-41c4-8f3f-be0de2750d43
-- title:
--   A real source of positive span has exactly two geometric greedy histories
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. For real source roots let u=(Σ_j a_j)/N, A=min_j a_j, and B=max_j a_j, with multiplicities retained. If n≥1 and A<B, there exist distinct complex location histories zL,zR such that an arbitrary z is an actual greedy history if and only if z=zL or z=zR.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyStatement.lean, lines 132-153, SHA-256 b0b4225b71610ef2d6a2e072dc060bf94cb556fe8b6c938713302f20f8d9fac9.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.real_greedy_exactly_two (n : ℕ) (hn : 1≤n) (a : Fin (n+1) → ℝ)
    (hspan : orderedSource a 0<orderedSource a (Fin.last n)) :
    ∃ zL zR : Fin (n+1) → ℂ, zL≠zR ∧
      ∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ↔
        z=zL ∨ z=zR := by sorry
