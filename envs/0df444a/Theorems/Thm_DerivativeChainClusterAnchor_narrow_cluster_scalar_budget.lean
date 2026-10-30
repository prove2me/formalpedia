-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_narrow_cluster_scalar_budget
-- name    : DerivativeChainClusterAnchor.narrow_cluster_scalar_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:42:22.406661+00:00
-- url     : https://prove2.me/theorems/db03116b-7644-4b42-85aa-6eb976ceba4e
-- title:
--   Exact narrow-cluster 7567-over-1920 scalar budget
-- statement:
--   For natural N≥16 and r>0 with 4r³≤N², suppose R,V,δ,ε≥0, V≤5(r/N)R², δ≤3(r/N)R, and ε≤R/(512N). Then (2r−1)√(V/(N−1))+√((2r−1)V/(N−1)+δ²)+4Nε+16r^(3/2)√(2Rε/N) ≤ (7567/1920)R.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterExplicitConstants.lean, lines 58-108, SHA-256 056babfcd4320c8d181f4874ddf2246c942c84f064f6c29ea488147504e1fa89. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
set_option maxHeartbeats 1500000
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.narrow_cluster_scalar_budget (n r : ℕ) (hn : 16 ≤ n) (hr : 0 < r)
    (hcube : 4*r^3 ≤ n^2) (R V δ ε : ℝ) (hR : 0 ≤ R) (hV0 : 0 ≤ V)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hV : V ≤ 5*((r:ℝ)/(n:ℝ))*R^2)
    (hδ : δ ≤ 3*((r:ℝ)/(n:ℝ))*R) (hε : ε ≤ R/(512*(n:ℝ))) :
    (2*(r:ℝ)-1)*Real.sqrt (V/((n:ℝ)-1))+
      Real.sqrt ((2*(r:ℝ)-1)*V/((n:ℝ)-1)+δ^2)+4*(n:ℝ)*ε+
      16*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (2*R*ε/(n:ℝ)) ≤ (7567/1920:ℝ)*R := by sorry
