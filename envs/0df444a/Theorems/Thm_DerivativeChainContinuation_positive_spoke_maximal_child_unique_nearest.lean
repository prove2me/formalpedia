-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_spoke_maximal_child_unique_nearest
-- name    : DerivativeChainContinuation.positive_spoke_maximal_child_unique_nearest
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:46:12.11692+00:00
-- url     : https://prove2.me/theorems/b93bed85-19e1-4640-b2c1-77a9276d71dd
-- title:
--   Every maximal nonzero child has one unique nearest spoke parent
-- statement:
--   A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2, Q has positive degree, and S=S_(k,r,Q) has degree at least two. Let w≠0 be an actual root of S′ with |z|≤|w| for every complex root z of S′. Then there is v with S(v)=0, |w|≤|v| and v=cw for some real c≥1. The value |v| is maximal among all complex roots of S, and every such root u satisfies |v-w|≤|u-w|, with |u-w|≤|v-w| only when u=v.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveSpokeNearest.lean, lines 102-147, SHA-256 d6c075d58f684a69fd40584387b2651dbcf018b1ad1c35ed2e0ae35f36d266f4.

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

theorem DerivativeChainContinuation.positive_spoke_maximal_child_unique_nearest (k s : ℕ) (Q : Polynomial ℝ)
    (hk : 2 ≤ k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (hdegree : 2 ≤ (spokePoly k s Q).natDegree)
    (w : ℂ) (hw : w≠0) (hroot : (spokePoly k s Q).derivative.eval w=0)
    (hmax : ∀ z : ℂ,(spokePoly k s Q).derivative.eval z=0 → ‖z‖ ≤ ‖w‖) :
    ∃ v : ℂ,(spokePoly k s Q).eval v=0 ∧ ‖w‖ ≤ ‖v‖ ∧
      (∃ c : ℝ,1 ≤ c ∧ v=(c : ℂ)*w) ∧
      (∀ u : ℂ,(spokePoly k s Q).eval u=0 → ‖u‖ ≤ ‖v‖) ∧
      ∀ u : ℂ,(spokePoly k s Q).eval u=0 →
        ‖v-w‖ ≤ ‖u-w‖ ∧ (‖u-w‖ ≤ ‖v-w‖ → u=v) := by sorry
