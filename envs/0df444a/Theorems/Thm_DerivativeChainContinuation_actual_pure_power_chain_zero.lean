-- Prove2me | Theorems.Thm_DerivativeChainContinuation_actual_pure_power_chain_zero
-- name    : DerivativeChainContinuation.actual_pure_power_chain_zero
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:11:50.369978+00:00
-- url     : https://prove2.me/theorems/b2de5cf5-b3d5-45f5-95f6-3ce25cbcef26
-- title:
--   Every actual chain of a pure power is the zero history
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. If p_a=X^N and z is any actual derivative chain, then z_i=0 for every i and L(z)=0. No nearest-parent hypothesis is required.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveActualRows.lean, lines 61-74, SHA-256 83f5f617266893ec1a3caef75bc2a46d2a3256859162ef0ed2116cfdd8c609d3.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.actual_pure_power_chain_zero {n : ℕ} (a z : Fin (n+1) → ℂ)
    (hp : fromRoots a=X^(n+1)) (hz : DerivativeChainPrivate.IsChain a z) :
    (∀ i,z i=0) ∧ chainCost z=0 := by sorry
