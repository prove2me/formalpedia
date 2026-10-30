-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_joint_complete_prefix_reserve
-- name    : DerivativeChainClusterAnchor.joint_complete_prefix_reserve
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:29:01.5204+00:00
-- url     : https://prove2.me/theorems/ba28af14-3ab0-4b50-9eac-53c9f0c6c498
-- title:
--   Joint prefix length and endpoint reserve
-- statement:
--   For a uniform polynomial-root tower through row h and any c, some row history z satisfies L(z)+|z_h−c| ≤ √(hV_h)+√(V_h+|r₀₀−c|²), where V_h is the uniform variance of row h about r₀₀.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterPrefix.lean, lines 29-79, SHA-256 fbc93a9cb66aa95dbb108ea5e4ad58106712bfaa487eb553da131a04ac463be4. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterPrefix
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.joint_complete_prefix_reserve (r : ComplexRootRows) (h : ℕ)
    (hstep : ∀ k<h, UniformPolynomialStep r k) (c : ℂ) :
    ∃ z : Fin (h+1) → ℂ, IsComplexRowHistory r z ∧
      chainCost z+‖z (Fin.last h)-c‖ ≤
        Real.sqrt ((h:ℝ)*rowCenteredVariance r h (r 0 0))+
          Real.sqrt (rowCenteredVariance r h (r 0 0)+‖r 0 0-c‖^2) := by sorry
