-- Prove2me | Theorems.Thm_DerivativeChainContinuation_affine_pure_power_unique_history
-- name    : DerivativeChainContinuation.affine_pure_power_unique_history
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:17:11.747253+00:00
-- url     : https://prove2.me/theorems/eedf82ff-3581-4d72-bb1c-e379217f1014
-- title:
--   A pure-power source has exactly one geometric greedy history
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. If p_a=X^N and o,c∈ℂ with c≠0, the set of actual greedy histories for source (o+ca_j)_j is precisely the singleton containing the constant history z_i=o. In particular a unique greedy history exists.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveRayCorollaries.lean, lines 186-203, SHA-256 7174fbbd4d36931f506b63017e7bd24da0afc12d26638665a78878a7c892072f.

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

theorem DerivativeChainContinuation.affine_pure_power_unique_history (n : ℕ) (a : Fin (n+1) → ℂ)
    (hp : fromRoots a=X^(n+1)) (o c : ℂ) (hc : c≠0) :
    {z : Fin (n+1) → ℂ | IsGreedyChain (fun i => o+c*a i) z}={fun _ => o} ∧
      (∃! z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*a i) z) := by sorry
