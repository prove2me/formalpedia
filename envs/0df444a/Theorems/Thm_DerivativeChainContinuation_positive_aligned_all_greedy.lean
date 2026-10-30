-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_aligned_all_greedy
-- name    : DerivativeChainContinuation.positive_aligned_all_greedy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:06:46.293986+00:00
-- url     : https://prove2.me/theorems/877daa05-b586-49cd-91c4-d7a20e5108d4
-- title:
--   Every positive aligned-ray greedy history costs the outer radius
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. A positive quotient Q∈ℝ[X] means Q≠0, Q splits over ℝ, and every element of its root multiset is strictly positive. Multiplicities are retained; nonzero constants satisfy this condition. For natural k,r write S_(k,r,Q)(X)=X^r Q(X^k)∈ℂ[X], mapping the real coefficients into ℂ. The central multiplicity r is arbitrary. Assume k≥2, Q has positive degree, and the actual monic source satisfies p_a=S_(k,r,Q). Actual greedy histories exist. There is a largest positive real root b of Q, and every actual greedy history z has L(z)=b^(1/k). At every degree m≥k its selected root is nonzero, has maximal norm among every complex root of P_m, and is c z_(k-1) for some real c≥1.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveGreedyStatement.lean, lines 9-52, SHA-256 ec998dcffb2e9eab4d0d16300f7b7ddc77c65dba7fc914c216ef324a5c231354.

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

theorem DerivativeChainContinuation.positive_aligned_all_greedy (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q) :
    (∃ z : Fin (n+1) → ℂ,IsGreedyChain a z) ∧
      ∃ b : ℝ,0<b ∧ Q.eval b=0 ∧ (∀ y : ℝ,Q.eval y=0 → y ≤ b) ∧
        ∀ z : Fin (n+1) → ℂ,IsGreedyChain a z →
          chainCost z=b^((k : ℝ)⁻¹) ∧
            ∀ i : Fin (n+1),k ≤ i.val+1 →
              z i≠0 ∧ (∀ w : ℂ,(row a (i.val+1)).eval w=0 → ‖w‖ ≤ ‖z i‖) ∧
                ∃ c : ℝ,1 ≤ c ∧ z i=(c : ℂ)*complexHistoryOf z (k-1) := by sorry
