-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_spoke_all_ordinary_rows
-- name    : DerivativeChainContinuation.positive_spoke_all_ordinary_rows
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:53:39.555472+00:00
-- url     : https://prove2.me/theorems/28537687-c18e-4483-8e40-39a02637fd76
-- title:
--   Every ordinary derivative row retains a positive spoke quotient
-- statement:
--   A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2 and deg(S_(k,r,Q))=N=n+1. For every 0≤j≤n, there exist s∈ℕ and a positive quotient V with the exact ordinary derivative identity S_(k,r,Q) differentiated j times = X^s V(X^k). The source Q may be constant.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveSpokeClosure.lean, lines 82-97, SHA-256 a7f35d5e8e76ba8593bb387f2e3bdf133b1cbfa84bd1a1f11e1864d47a1f8202.

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

theorem DerivativeChainContinuation.positive_spoke_all_ordinary_rows (n k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q)
    (hdegree : (spokePoly k r Q).natDegree=n+1) :
    ∀ j≤n, ∃ s : ℕ, ∃ V : Polynomial ℝ, PositiveQuotient V ∧
      derivative^[j] (spokePoly k r Q)=spokePoly k s V := by sorry
