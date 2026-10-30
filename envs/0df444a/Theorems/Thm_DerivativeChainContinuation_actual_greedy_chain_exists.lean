-- Prove2me | Theorems.Thm_DerivativeChainContinuation_actual_greedy_chain_exists
-- name    : DerivativeChainContinuation.actual_greedy_chain_exists
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:10:02.555117+00:00
-- url     : https://prove2.me/theorems/d1ffd762-a6ea-4257-b40e-6b9dfd26ab2e
-- title:
--   Every nonempty complex source has an actual nearest-parent chain
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. For every n∈ℕ and arbitrary source tuple a∈ℂ^(n+1), an actual greedy history exists.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/GreedyExistence.lean, lines 6-54, SHA-256 09b3b38f910498b7fb2ec4fe6fef66759a7a6debc03a2a5cad76b7acecfe5d5e.

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

theorem DerivativeChainContinuation.actual_greedy_chain_exists (n : ℕ) (a : Fin (n+1) → ℂ) :
    ∃ z : Fin (n+1) → ℂ,IsGreedyChain a z := by sorry
