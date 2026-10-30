-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_activation_parameter_formula
-- name    : DerivativeChainContinuation.positive_activation_parameter_formula
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:19:16.038191+00:00
-- url     : https://prove2.me/theorems/37fbb793-215d-4795-ad87-c8386ef1ec4e
-- title:
--   The actual activation parameter is the root sum divided by a binomial coefficient
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2, Q has positive degree, and the actual monic source satisfies p_a=S_(k,r,Q). Let A_Q be the sum of the complete root multiset of Q, including multiplicities. Then A_Q/choose(N,k)>0, and for every z∈ℂ, P_k(z)=0 if and only if z^k=A_Q/choose(N,k), embedding the real quotient into ℂ.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveRayCorollaries.lean, lines 236-301, SHA-256 7174fbbd4d36931f506b63017e7bd24da0afc12d26638665a78878a7c892072f.

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

theorem DerivativeChainContinuation.positive_activation_parameter_formula (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q) :
    0<Q.roots.sum/(Nat.choose (n+1) k : ℝ) ∧
      ∀ z : ℂ,(row a k).eval z=0 ↔ z^k=((Q.roots.sum/(Nat.choose (n+1) k : ℝ) : ℝ) : ℂ) := by sorry
