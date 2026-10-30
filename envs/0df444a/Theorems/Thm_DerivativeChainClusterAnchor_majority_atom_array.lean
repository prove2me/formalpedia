-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_majority_atom_array
-- name    : DerivativeChainClusterAnchor.majority_atom_array
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:58:27.882503+00:00
-- url     : https://prove2.me/theorems/e50f4f2e-7520-4763-a55d-25cda4959774
-- title:
--   Actual root-slot atom chain bound
-- statement:
--   Let a have N=n+1 slots in D(o,R), R≥0. Let r³≤N² and |O|≤r, suppose c occurs as an actual slot, and every non-outlier equals c. Then the slot-product polynomial has a complete actual derivative-root chain of length at most (2+√2)R. Zero actual outliers and small degrees are included.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterAtom.lean, lines 12-69, SHA-256 c8dc21e9e7eb435c6e5e83de3b5db8116f8b43919a189092fe2f2cd13cb80e2f. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
open DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.majority_atom_array (n r : ℕ) (a : Fin (n+1) → ℂ) (o c : ℂ)
    (O : Finset (Fin (n+1))) (R : ℝ) (hcube : r^3 ≤ (n+1)^2) (hO : O.card ≤ r)
    (hR : 0 ≤ R) (hsource : ∀ i, ‖a i-o‖ ≤ R) (hc : ∃ i, a i=c)
    (hnear : ∀ i, i ∉ O → a i=c) :
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧ chainCost z ≤ (2+Real.sqrt 2)*R := by sorry
