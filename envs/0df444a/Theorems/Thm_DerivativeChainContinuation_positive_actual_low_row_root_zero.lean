-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_actual_low_row_root_zero
-- name    : DerivativeChainContinuation.positive_actual_low_row_root_zero
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:00:33.417121+00:00
-- url     : https://prove2.me/theorems/bed917df-4a38-4ca3-817f-e0159e198a39
-- title:
--   Every actual row before activation is supported at zero
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2 and p_a=S_(k,r,Q). For every 1≤m≤N with m<k, every complex root of P_m equals zero. Nonconstant Q is not required.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveActualRows.lean, lines 36-44, SHA-256 83f5f617266893ec1a3caef75bc2a46d2a3256859162ef0ed2116cfdd8c609d3.

import Mathlib
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

theorem DerivativeChainContinuation.positive_actual_low_row_root_zero {n : ℕ} (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hp : fromRoots a=spokePoly k r Q) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1)
    (hmlow : m<k) (z : ℂ) (hroot : (row a m).eval z=0) : z=0 := by sorry
