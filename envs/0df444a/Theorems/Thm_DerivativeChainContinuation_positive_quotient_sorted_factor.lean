-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_quotient_sorted_factor
-- name    : DerivativeChainContinuation.positive_quotient_sorted_factor
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:38:51.87561+00:00
-- url     : https://prove2.me/theorems/f0aa6ed5-ff0f-4d1d-b402-65381de8b09e
-- title:
--   A positive quotient has a complete sorted factorization
-- statement:
--   A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. There exist n∈ℕ and a monotone tuple a∈ℝ^n with every a_i>0, n=deg(Q), and Q=leadingCoeff(Q)·∏_(i=0)^(n-1)(X-a_i). Nonzero constants are included with n=0.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveQuotientRoots.lean, lines 7-31, SHA-256 629c8d98288aff6a03e95c2500b6516b0d2c6aad74ffd1548a207d8a23ac33aa.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_quotient_sorted_factor (Q : Polynomial ℝ) (hQ : PositiveQuotient Q) :
    ∃ n : ℕ,∃ a : Fin n → ℝ, Monotone a ∧ (∀ i,0<a i) ∧
      n=Q.natDegree ∧ Q=C Q.leadingCoeff*realRootProduct a := by sorry
