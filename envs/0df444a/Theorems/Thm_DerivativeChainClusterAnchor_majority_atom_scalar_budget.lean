-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_majority_atom_scalar_budget
-- name    : DerivativeChainClusterAnchor.majority_atom_scalar_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:54:42.573883+00:00
-- url     : https://prove2.me/theorems/60c999a0-c9e1-47b6-81ce-ce59f32d9af5
-- title:
--   Exact atom scalar budget at two plus square root two
-- statement:
--   For natural N≥8 and r>0 with r³≤N², let R,V,δ≥0 satisfy V≤4(r/N)(1−r/N)R² and δ≤2(r/N)R. Then (r−1)√(V/(N−1))+√((r−1)V/(N−1)+δ²)≤(2+√2)R.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterAtomConstants.lean, lines 6-59, SHA-256 56eab79f410aede846d263a613bd347197e569d754cca08749da063bf1ebb0e6. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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

theorem DerivativeChainClusterAnchor.majority_atom_scalar_budget (n r : ℕ) (hn : 8 ≤ n) (hr : 0 < r)
    (hcube : r^3 ≤ n^2) (R V δ : ℝ) (hR : 0 ≤ R) (hV0 : 0 ≤ V) (hδ0 : 0 ≤ δ)
    (hV : V ≤ 4*((r:ℝ)/(n:ℝ))*(1-(r:ℝ)/(n:ℝ))*R^2)
    (hδ : δ ≤ 2*((r:ℝ)/(n:ℝ))*R) :
    ((r:ℝ)-1)*Real.sqrt (V/((n:ℝ)-1))+
      Real.sqrt (((r:ℝ)-1)*V/((n:ℝ)-1)+δ^2) ≤ (2+Real.sqrt 2)*R := by sorry
