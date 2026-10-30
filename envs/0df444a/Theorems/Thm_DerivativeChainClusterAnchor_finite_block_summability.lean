-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_finite_block_summability
-- name    : DerivativeChainClusterAnchor.finite_block_summability
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T22:46:53.149839+00:00
-- url     : https://prove2.me/theorems/f08c38b0-7663-48e7-b8fd-cc09280b12f2
-- title:
--   Finite reciprocal three-halves block sum
-- statement:
--   For every natural N, the sum of 1/((j+2)√(j+2)) over 0≤j<N is at most 2.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterBlockEstimates.lean, lines 63-77, SHA-256 7acd9283ebb93b802b861040fe9fcb68d8685864ceace1397fc9d82bf56d2526. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
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
set_option maxHeartbeats 1000000
open scoped BigOperators
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.finite_block_summability (N : ℕ) :
    (∑ j ∈ Finset.range N, 1/((j+2:ℝ)*Real.sqrt (j+2:ℝ))) ≤ 2 := by sorry
