-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_majority_atom_source_variance
-- name    : DerivativeChainClusterAnchor.majority_atom_source_variance
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:56:31.041306+00:00
-- url     : https://prove2.me/theorems/1d6d5484-1c95-411e-98a0-ebfa03cd0902
-- title:
--   Sharp variance bound for a disk source with an exact atom
-- statement:
--   Let a have N>0 slots in D(o,R), with R≥0 and c∈D(o,R). Suppose |O|≤r, 2r≤N and every non-outlier equals c. If u is the uniform source mean, then its variance is at most 4(r/N)(1−r/N)R².
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSourceMoments.lean, lines 97-136, SHA-256 e1a1f7e09ebb1a081db2b09f4b6eb005daaf0638fea2eeef285ac0720a59e540. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.majority_atom_source_variance {n r : ℕ} (a : Fin n → ℂ) (c o u : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hO : O.card ≤ r) (hhalf : 2*r ≤ n)
    (R : ℝ) (hR : 0 ≤ R) (hc : ‖c-o‖ ≤ R) (hall : ∀ i, ‖a i-o‖ ≤ R)
    (hnear : ∀ i, i ∉ O → a i=c)
    (hmean : (∑ i, (((n:ℝ)⁻¹:ℝ):ℂ)*a i)=u) :
    (∑ i, (n:ℝ)⁻¹*‖a i-u‖^2) ≤ 4*((r:ℝ)/(n:ℝ))*(1-(r:ℝ)/(n:ℝ))*R^2 := by sorry
