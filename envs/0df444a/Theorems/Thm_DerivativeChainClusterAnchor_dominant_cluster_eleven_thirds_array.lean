-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_dominant_cluster_eleven_thirds_array
-- name    : DerivativeChainClusterAnchor.dominant_cluster_eleven_thirds_array
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:39:00.137262+00:00
-- url     : https://prove2.me/theorems/1bb9ff88-cf7e-4e0c-a95d-1be75ac34656
-- title:
--   Actual root-slot clustered-source eleven-thirds chain bound
-- statement:
--   Let a have N=n+1≥16 complex root slots in D(o,R), with R,ε≥0 and c∈D(o,R). Suppose r>0, 16r³≤N², |O|≤r, ε≤R/(16N), and every non-outlier lies within ε of c. There is one complete actual derivative-root chain of ∏ᵢ(X−aᵢ) with length at most (11/3)R, and with length strictly below 4R if R>0. Repeated slots and ε=0 are allowed.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterMain.lean, lines 64-94, SHA-256 2b5234892f131152ed03c6c2f34bed0530ec0d7e53cbfad2b4468411f3de2c49. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.dominant_cluster_eleven_thirds_array (n r : ℕ) (a : Fin (n+1) → ℂ)
    (o c : ℂ) (O : Finset (Fin (n+1))) (R ε : ℝ) (hn : 16 ≤ n+1) (hr : 0 < r)
    (hcube : 16*r^3 ≤ (n+1)^2) (hO : O.card ≤ r) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hsmall : ε ≤ R/(16*(n+1:ℝ))) (hsource : ∀ i, ‖a i-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) :
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧
      chainCost z ≤ (11/3:ℝ)*R ∧ (0 < R → chainCost z < 4*R) := by sorry
