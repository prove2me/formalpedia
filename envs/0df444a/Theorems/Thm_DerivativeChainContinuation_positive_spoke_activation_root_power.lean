-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_spoke_activation_root_power
-- name    : DerivativeChainContinuation.positive_spoke_activation_root_power
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:22:29.232159+00:00
-- url     : https://prove2.me/theorems/fd72f34e-44f9-40f8-87a1-061696f01e13
-- title:
--   The complete activation zero set is one nonzero regular orbit
-- statement:
--   A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2, Q has positive degree, and S_(k,r,Q) has degree N=n+1. There is a real b>0 such that, for every z∈ℂ, the ordinary derivative of order N-k vanishes at z if and only if z^k=b.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveActivation.lean, lines 97-120, SHA-256 f08e9155f45a8e955a6385fca442b49a8cce7ab81cc0d6b3cc4d14e117a1c946.

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

theorem DerivativeChainContinuation.positive_spoke_activation_root_power (n k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (hdegree : (spokePoly k r Q).natDegree=n+1) :
    ∃ b : ℝ,0<b ∧ ∀ z : ℂ,
      (derivative^[n+1-k] (spokePoly k r Q)).eval z=0 ↔ z^k=(b : ℂ) := by sorry
