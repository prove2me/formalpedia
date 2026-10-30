-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_cluster_source_centroid_variance
-- name    : DerivativeChainClusterAnchor.cluster_source_centroid_variance
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:35:22.765037+00:00
-- url     : https://prove2.me/theorems/269b1d50-af30-4e90-9698-ee26e5fb21a3
-- title:
--   Variance and centroid displacement from a clustered slot list
-- statement:
--   Let a have N>0 complex slots and uniform mean u. Let |O|≤r, ε,D≥0, all slots satisfy |aᵢ−c|≤D, and non-outliers satisfy |aᵢ−c|≤ε. Then the uniform variance about u is at most ε²+(r/N)D², and |u−c|≤ε+(r/N)D. No ε≤D condition is imposed.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSourceMoments.lean, lines 33-55, SHA-256 e1a1f7e09ebb1a081db2b09f4b6eb005daaf0638fea2eeef285ac0720a59e540. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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

theorem DerivativeChainClusterAnchor.cluster_source_centroid_variance {n r : ℕ} (a : Fin n → ℂ) (c u : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D)
    (hmean : (∑ i, (((n:ℝ)⁻¹:ℝ):ℂ)*a i)=u) :
    (∑ i, (n:ℝ)⁻¹*‖a i-u‖^2) ≤ ε^2+(r:ℝ)/(n:ℝ)*D^2 ∧
      ‖u-c‖ ≤ ε+(r:ℝ)/(n:ℝ)*D := by sorry
