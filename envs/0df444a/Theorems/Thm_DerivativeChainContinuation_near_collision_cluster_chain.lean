-- Prove2me | Theorems.Thm_DerivativeChainContinuation_near_collision_cluster_chain
-- name    : DerivativeChainContinuation.near_collision_cluster_chain
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:05:10.712244+00:00
-- url     : https://prove2.me/theorems/75c4dfc7-1e80-4f63-aade-3b0123f009eb
-- title:
--   Complete cluster chains with an original containing disk
-- statement:
--   Let $p=\prod_{i=0}^{n}(X-a_i)$ with source centroid $u$, and suppose $a_i\in D(o,R)$, $R\ge0$. If every proper-row root has local uniform mass at least $1/K$ in its closed radius-$\rho_k$ ball, with $K>0$ and $\sum_k\rho_k\le B$, then one complete actual derivative-root chain satisfies $$L\le K\sqrt{2(R^2-|u-o|^2)}+2B.$$ Degree one, repeated roots, pure powers and zero-radius containing disks are included.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollisionCluster.lean#L36-L61

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_PolynomialNearCollision
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem DerivativeChainContinuation.near_collision_cluster_chain (n : ℕ) (a : Fin (n+1) → ℂ)
    (ρ : ℕ → ℝ) (K B : ℝ) (hK : 0 < K)
    (hmass : ∀ k<n,∀ x : ℂ,(derivative^[n-k] (fromRoots a)).eval x=0 →
      K⁻¹ ≤ polynomialLocalMass (derivative^[n-k] (fromRoots a)) x (ρ k))
    (hbudget : (∑ k ∈ Finset.range n,ρ k) ≤ B)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i,‖a i-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧
      chainCost z ≤ K*Real.sqrt (2*(R^2-‖complexCentroid a-o‖^2))+2*B := by sorry
