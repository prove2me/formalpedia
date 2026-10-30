-- Prove2me | Theorems.Thm_DerivativeChainContinuation_actual_real_greedy_classification
-- name    : DerivativeChainContinuation.actual_real_greedy_classification
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:53:36.745932+00:00
-- url     : https://prove2.me/theorems/b436eab9-3025-40ba-bbbf-5ea9145a9928
-- title:
--   Complete greedy classification for a sorted real source
-- statement:
--   For a nonempty labelled tuple a=(a_0,…,a_n)∈ℂ^(n+1), put N=n+1 and p_a(X)=∏_(j=0)^n(X-a_j). Its ordinary row of degree m is P_m=p_a differentiated N-m times, for 1≤m≤N. An actual greedy location history z=(z_0,…,z_n) satisfies P_(i+1)(z_i)=0 and |z_(i+1)-z_i|≤|w-z_i| for every i<n and every complex root w of P_(i+2). Its length is L(z)=Σ_(i=0)^(n-1)|z_(i+1)-z_i|. Repeated root values and every local tie are allowed. For real source roots let u=(Σ_j a_j)/N, A=min_j a_j, and B=max_j a_j, with multiplicities retained. Assume n≥1 and the source tuple a is monotone. There is a monotone real root list r_k of length k+1 for every ordinary row, with the source tuple as the top row and the exact derivative relation between consecutive row products. Every complex root of every actual row is an entry of that real row list. An actual greedy history is exactly one of the complete smallest-root and largest-root histories. Their lengths are u-A and B-u, respectively, and a greedy history of length at most (B-A)/2 exists.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyActual.lean, lines 93-149, SHA-256 d3ac9fdd06dd387e730b07299cffea9935de88f557ffb857e687a74f824fca1d.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.actual_real_greedy_classification (n : ℕ) (hn : 1≤n)
    (a : Fin (n+1) → ℝ) (ha : Monotone a) :
    ∃ r : RealRows, r n=a ∧
      (∀ k≤n,Monotone (r k)) ∧ (∀ k<n,RealRowStep r k) ∧
      (∀ k≤n,∀ w : ℂ,
        (row (fun i => (a i : ℂ)) (k+1)).eval w=0 ↔
          ∃ j : Fin (k+1),w=(r k j : ℂ)) ∧
      (∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ↔
        (∀ i,z i=(leftRow r i.val : ℂ)) ∨
        (∀ i,z i=(rightRow r i.val : ℂ))) ∧
      (∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z →
        chainCost z=realCentroid a-a 0 ∨
        chainCost z=a (Fin.last n)-realCentroid a) ∧
      (∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
        chainCost z≤(a (Fin.last n)-a 0)/2) := by sorry
