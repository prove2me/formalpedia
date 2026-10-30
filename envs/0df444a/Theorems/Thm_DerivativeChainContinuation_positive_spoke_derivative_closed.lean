-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_spoke_derivative_closed
-- name    : DerivativeChainContinuation.positive_spoke_derivative_closed
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:42:47.228928+00:00
-- url     : https://prove2.me/theorems/c1664082-443f-4739-8820-ad0a1712d1e2
-- title:
--   Differentiation preserves the full positive spoke class
-- statement:
--   A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. If k≥2 and the degree of S_(k,r,Q) is at least two, then there exist s∈ℕ and a positive quotient V such that S_(k,r,Q)′=X^s V(X^k). No upper bound on the central exponent r is assumed.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveSpokeClosure.lean, lines 53-72, SHA-256 a7f35d5e8e76ba8593bb387f2e3bdf133b1cbfa84bd1a1f11e1864d47a1f8202.

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

theorem DerivativeChainContinuation.positive_spoke_derivative_closed (k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q)
    (hdegree : 2≤(spokePoly k r Q).natDegree) :
    ∃ s : ℕ, ∃ V : Polynomial ℝ, PositiveQuotient V ∧
      (spokePoly k r Q).derivative=spokePoly k s V := by sorry
