-- Prove2me | Theorems.Thm_DerivativeChainContinuation_affine_pure_power_greedy_zero
-- name    : DerivativeChainContinuation.affine_pure_power_greedy_zero
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:13:51.958773+00:00
-- url     : https://prove2.me/theorems/3f847edf-c1da-4298-a78d-fd3b13546bcc
-- title:
--   Pure-power greedy histories stay at their affine center
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. Assume p_a=X^N. For any o,c∈ℂ with c≠0 and every actual greedy history z for source (o+ca_j)_j, z_i=o for every i and L(z)=0.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveGreedyStatement.lean, lines 115-130, SHA-256 ec998dcffb2e9eab4d0d16300f7b7ddc77c65dba7fc914c216ef324a5c231354.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.affine_pure_power_greedy_zero (n : ℕ) (a z : Fin (n+1) → ℂ)
    (hp : fromRoots a=X^(n+1)) (o c : ℂ) (hc : c≠0)
    (hz : IsGreedyChain (fun i => o+c*a i) z) :
    (∀ i,z i=o) ∧ chainCost z=0 := by sorry
