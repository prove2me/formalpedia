-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_dominant_cluster_eleven_thirds
-- name    : DerivativeChainClusterAnchor.dominant_cluster_eleven_thirds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:40:55.304919+00:00
-- url     : https://prove2.me/theorems/0e08262c-a1ce-42eb-b666-81dc84bddc67
-- title:
--   Full monic-polynomial dominant-cluster eleven-thirds bound
-- statement:
--   Let p be monic of exact degree N≥16. Suppose r>0 and 16r³≤N², every root occurrence lies in D(o,R), c∈D(o,R), R,ε≥0 and ε≤R/(16N). If at most r root occurrences lie strictly outside D(c,ε), one complete selection from the derivative rows p^(N−1),…,p exists with total adjacent-point length at most (11/3)R, and strictly below 4R when R>0. Counts retain multiplicity; c need not be a root and no endpoint is prescribed.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterPolynomial.lean, lines 28-48, SHA-256 c2d11b703110b89e571e83fb606d9fc27e81cf4babb7a2167e1274266ce0f735. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.dominant_cluster_eleven_thirds (p : ℂ[X]) (hp : p.Monic) (n r : ℕ)
    (hdegree : p.natDegree=n) (hn : 16 ≤ n) (hr : 0 < r) (hcube : 16*r^3 ≤ n^2)
    (o c : ℂ) (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hsmall : ε ≤ R/(16*(n:ℝ)))
    (hsource : ∀ z ∈ p.roots, ‖z-o‖ ≤ R) (hc : ‖c-o‖ ≤ R)
    (hcluster : (p.roots.filter (fun z => ε < ‖z-c‖)).card ≤ r) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      chainCost z ≤ (11/3:ℝ)*R ∧ (0 < R → chainCost z < 4*R) := by sorry
