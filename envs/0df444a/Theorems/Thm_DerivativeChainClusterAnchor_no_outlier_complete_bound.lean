-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_no_outlier_complete_bound
-- name    : DerivativeChainClusterAnchor.no_outlier_complete_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:05:45.658772+00:00
-- url     : https://prove2.me/theorems/3d627606-3c14-41cd-981a-bc90bb0a7b73
-- title:
--   No-outlier monic chain bound at radius over sixteen
-- statement:
--   Let p be monic of exact degree N>0, let R,ε≥0 with ε≤R/(16N), and suppose every actual root lies in D(c,ε). Then one complete derivative-root selection has length at most R/16 and, if R>0, strictly below 4R. No separate source-disk center or prescribed endpoint is assumed.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterDegenerate.lean, lines 8-26, SHA-256 701edb2d177ddaf66ec04b2b1e40170734a471817faa13ff466a7d2e4cbe7ac7. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
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
open Polynomial DerivativeChainPrivate
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.no_outlier_complete_bound (p : ℂ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree=n) (hn : 0 < n) (c : ℂ) (R ε : ℝ) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) (hsmall : ε ≤ R/(16*(n:ℝ))) (hsource : ∀ z ∈ p.roots, ‖z-c‖ ≤ ε) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      chainCost z ≤ R/16 ∧ (0 < R → chainCost z < 4*R) := by sorry
