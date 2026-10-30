-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_cluster_envelope
-- name    : DerivativeChainClusterAnchor.ordinaryRow_cluster_envelope
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:19:09.046449+00:00
-- url     : https://prove2.me/theorems/020ae8e7-cc39-42ca-9155-ec5f842621df
-- title:
--   Normalized derivative envelope for a clustered source
-- statement:
--   Let n>0 and m≤n. Suppose at most r outlier slots lie within distance D of c and all other root slots lie within ε, where 0<ε≤D. Then |Qₘ(c)| ≤ ε^m(1+Dm/(nε))^r.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSourceBound.lean, lines 29-65, SHA-256 19ac62494cf8f963d7a0bd40c2bb19da7b4e5cfd2025a50830fde6359b03822e. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
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
open Finset Polynomial
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.ordinaryRow_cluster_envelope {n m r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hm : m ≤ n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 < ε) (hεD : ε ≤ D)
    (hnear : ∀ i, i ∉ O → ‖c-a i‖ ≤ ε) (hfar : ∀ i, i ∈ O → ‖c-a i‖ ≤ D) :
    ‖(ordinaryRow a m).eval c‖ ≤ ε^m*(1+D*(m:ℝ)/((n:ℝ)*ε))^r := by sorry
