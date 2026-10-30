-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_source_cluster_disk_moments
-- name    : DerivativeChainClusterAnchor.source_cluster_disk_moments
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:36:52.470549+00:00
-- url     : https://prove2.me/theorems/b4051555-40d7-412e-ab1b-293df3d184cf
-- title:
--   Actual disk-source moment bounds for a dominant cluster
-- statement:
--   Let a have N=n+1 slots in D(o,R), with R,ε≥0 and cluster center c∈D(o,R). Suppose r>0, |O|≤r, ε≤R/N and non-outliers lie within ε of c. Every slot lies within 2R of c; the uniform source variance is at most 5(r/N)R²; and the source centroid lies within 3(r/N)R of c.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterMain.lean, lines 19-53, SHA-256 2b5234892f131152ed03c6c2f34bed0530ec0d7e53cbfad2b4468411f3de2c49. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.source_cluster_disk_moments (n r : ℕ) (a : Fin (n+1) → ℂ) (c o : ℂ)
    (O : Finset (Fin (n+1))) (hr : 0 < r) (hO : O.card ≤ r) (R ε : ℝ)
    (hR : 0 ≤ R) (hε : 0 ≤ ε) (hsmall : ε ≤ R/(n+1:ℝ))
    (hsource : ∀ i, ‖a i-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) :
    (∀ i, ‖a i-c‖ ≤ 2*R) ∧
      (∑ i, (n+1:ℝ)⁻¹*‖a i-complexCentroid a‖^2) ≤ 5*((r:ℝ)/(n+1:ℝ))*R^2 ∧
      ‖complexCentroid a-c‖ ≤ 3*((r:ℝ)/(n+1:ℝ))*R := by sorry
