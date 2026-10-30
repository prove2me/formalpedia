-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_actual_greedy_step
-- name    : DerivativeChainContinuation.positive_actual_greedy_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:49:14.917063+00:00
-- url     : https://prove2.me/theorems/a0a132d9-d3bd-455b-bfc9-ae18cf6e6542
-- title:
--   An actual greedy step preserves the maximal selected ray
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2, Q has positive degree, and the actual monic source satisfies p_a=S_(k,r,Q). Let z be an actual greedy history and let k≤m≤n. Assume the selected degree-m root z_(m-1) is nonzero and has maximal norm among every complex root of P_m. Then z_m is nonzero, has maximal norm among every complex root of P_(m+1), and z_m=c z_(m-1) for some real c≥1.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveGreedyChain.lean, lines 30-70, SHA-256 58c5c71ff2fb47b0e8104dc20db7e478834107a3be76a063f1be761fb21e1c74.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
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

theorem DerivativeChainContinuation.positive_actual_greedy_step {n : ℕ} (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q)
    (hz : IsGreedyChain a z) (m : ℕ) (hm : k ≤ m) (hmn : m ≤ n)
    (hw : complexHistoryOf z (m-1)≠0)
    (hmax : ∀ w : ℂ,(row a m).eval w=0 → ‖w‖ ≤ ‖complexHistoryOf z (m-1)‖) :
    complexHistoryOf z m≠0 ∧
      (∀ w : ℂ,(row a (m+1)).eval w=0 → ‖w‖ ≤ ‖complexHistoryOf z m‖) ∧
      ∃ c : ℝ,1 ≤ c ∧ complexHistoryOf z m=(c : ℂ)*complexHistoryOf z (m-1) := by sorry
