-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_constant_affine_greedy_zero
-- name    : DerivativeChainContinuation.positive_constant_affine_greedy_zero
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:14:53.298119+00:00
-- url     : https://prove2.me/theorems/0882c7cf-f706-4cc3-9d28-9f173b1b3b64
-- title:
--   A constant positive quotient gives zero-cost greedy histories at the center
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2, deg(Q)=0 and p_a=S_(k,r,Q). For arbitrary o,c∈ℂ with c≠0, every actual greedy history for source (o+ca_j)_j has all entries equal to o and total length zero.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveGreedyStatement.lean, lines 151-157, SHA-256 ec998dcffb2e9eab4d0d16300f7b7ddc77c65dba7fc914c216ef324a5c231354.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_constant_affine_greedy_zero (n : ℕ) (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : Q.natDegree=0) (hp : fromRoots a=spokePoly k r Q)
    (o c : ℂ) (hc : c≠0) (hz : IsGreedyChain (fun i => o+c*a i) z) :
    (∀ i,z i=o) ∧ chainCost z=0 := by sorry
