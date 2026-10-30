-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_prefix_component_squares
-- name    : DerivativeChainClusterAnchor.prefix_component_squares
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:31:33.877578+00:00
-- url     : https://prove2.me/theorems/5bc4a27a-83f7-46be-9805-2e5e59cff0f1
-- title:
--   Squared prefix-budget components under source moment bounds
-- statement:
--   Let N,q,R,V,δ be real with N>1, q≥1, 2q≤N and R,V,δ≥0. If V≤5(q/N)R² and δ≤3(q/N)R, then ((2q−1)√(V/(N−1)))²≤20q³R²/(N(N−1)) and (√((2q−1)V/(N−1)+δ²))²≤19(q/N)²R².
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterConstants.lean, lines 18-48, SHA-256 03aff2e3679cb0de99930439379cba9933534dd16e42af667b55b46c8034d885. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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

theorem DerivativeChainClusterAnchor.prefix_component_squares (N q R V δ : ℝ) (hN : 1 < N) (hq : 1 ≤ q)
    (hcut : 2*q ≤ N) (hR : 0 ≤ R) (hV0 : 0 ≤ V) (hδ0 : 0 ≤ δ)
    (hV : V ≤ 5*(q/N)*R^2) (hδ : δ ≤ 3*(q/N)*R) :
    ((2*q-1)*Real.sqrt (V/(N-1)))^2 ≤ 20*q^3*R^2/(N*(N-1)) ∧
      (Real.sqrt ((2*q-1)*V/(N-1)+δ^2))^2 ≤ 19*(q/N)^2*R^2 := by sorry
