-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_source_cluster_tail_bound
-- name    : DerivativeChainClusterAnchor.source_cluster_tail_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:23:10.764362+00:00
-- url     : https://prove2.me/theorems/ff6bc0e5-f8a1-4997-aae2-8c87009763b0
-- title:
--   Cluster anchor-tail bound with ε≤D
-- statement:
--   Let a have n complex root slots, let r>0 with 2r<n, and let |O|≤r. Assume ε≥0, ε≤D, every non-outlier satisfies |aᵢ−c|≤ε, and every slot satisfies |aᵢ−c|≤D. Then Σₘ₌₂ᵣ₊₁ⁿ |Qₘ(c)|^(1/m) ≤ 2nε+8r^(3/2)√(Dε/n). Multiplicities and ε=0 are permitted.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterTail.lean, lines 125-159, SHA-256 1f8def0926d0c974316163c75b78814a53c991a712c49f9ef7f8629386e09304. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterTail
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Finset Polynomial
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.source_cluster_tail_bound {n r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hr : 0 < r) (hcut : 2*r < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε) (hεD : ε ≤ D)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D) :
    (∑ m ∈ Finset.Icc (2*r+1) n, anchorRadius a c m) ≤
      2*(n:ℝ)*ε+8*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (D*ε/(n:ℝ)) := by sorry
