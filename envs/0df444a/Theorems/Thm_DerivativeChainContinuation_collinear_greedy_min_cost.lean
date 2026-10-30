-- Prove2me | Theorems.Thm_DerivativeChainContinuation_collinear_greedy_min_cost
-- name    : DerivativeChainContinuation.collinear_greedy_min_cost
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T21:15:32.229902+00:00
-- url     : https://prove2.me/theorems/48996ec4-2a03-47fe-ba71-e8950ccd9d6d
-- title:
--   The least greedy cost on a complex line is attained
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. For real source roots let u=(Σ_j a_j)/N, A=min_j a_j, and B=max_j a_j, with multiplicities retained. Let o,c∈ℂ with c≠0 and use source (o+ca_j)_j. For n≥1, an actual greedy history attains length |c|min(u-A,B-u). Its length is no greater than that of every other actual greedy history, and is at most |c|(B-A)/2.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyAffine.lean, lines 86-106, SHA-256 5199684125a29b206d508d42c435db1c20a7cb0da21008d4e73cd13b18831f83.

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

theorem DerivativeChainContinuation.collinear_greedy_min_cost (n : ℕ) (hn : 1 ≤ n) (a : Fin (n+1) → ℝ)
    (o c : ℂ) (hc : c≠0) :
    ∃ z : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*(a i : ℂ)) z ∧
      chainCost z=‖c‖*min (realCentroid a-orderedSource a 0)
        (orderedSource a (Fin.last n)-realCentroid a) ∧
      (∀ w : Fin (n+1) → ℂ,IsGreedyChain (fun i => o+c*(a i : ℂ)) w → chainCost z ≤ chainCost w) ∧
      chainCost z ≤ ‖c‖*(orderedSource a (Fin.last n)-orderedSource a 0)/2 := by sorry
