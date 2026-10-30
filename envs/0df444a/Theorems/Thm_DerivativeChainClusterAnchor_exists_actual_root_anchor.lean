-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_exists_actual_root_anchor
-- name    : DerivativeChainClusterAnchor.exists_actual_root_anchor
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:27:36.137324+00:00
-- url     : https://prove2.me/theorems/37e0d2f7-db22-4b85-b6e6-44ee5d25b153
-- title:
--   An actual polynomial root within the evaluation anchor radius
-- statement:
--   If p is a monic complex polynomial of positive degree m, then for every c there is an actual root z of p with |z−c|≤|p(c)|^(1/m).
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterRows.lean, lines 60-85, SHA-256 61e88b87458232a2a943f9e33b7c47119da33fd482ec9698694001c678af47d3. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
open Polynomial
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.exists_actual_root_anchor (p : ℂ[X]) (hp : p.Monic) (m : ℕ)
    (hm : 0 < m) (hdegree : p.natDegree=m) (c : ℂ) :
    ∃ z : ℂ, p.eval z=0 ∧ ‖z-c‖ ≤ ‖p.eval c‖^((m:ℝ)⁻¹) := by sorry
