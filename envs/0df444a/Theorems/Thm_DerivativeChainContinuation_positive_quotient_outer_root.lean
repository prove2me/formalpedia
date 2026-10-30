-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_quotient_outer_root
-- name    : DerivativeChainContinuation.positive_quotient_outer_root
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:26:41.329095+00:00
-- url     : https://prove2.me/theorems/a880c12f-6635-4589-a452-2365280a8522
-- title:
--   A nonconstant positive quotient has a largest positive root
-- statement:
--   A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. If Q has positive degree, there is b>0 with Q(b)=0 and y≤b for every real y satisfying Q(y)=0.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveSpokeNearest.lean, lines 82-100, SHA-256 d6c075d58f684a69fd40584387b2651dbcf018b1ad1c35ed2e0ae35f36d266f4.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_quotient_outer_root (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) :
    ∃ b : ℝ,0<b ∧ Q.eval b=0 ∧ ∀ y : ℝ,Q.eval y=0 → y ≤ b := by sorry
