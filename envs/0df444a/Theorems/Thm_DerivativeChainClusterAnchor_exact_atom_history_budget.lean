-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_exact_atom_history_budget
-- name    : DerivativeChainClusterAnchor.exact_atom_history_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:52:55.907711+00:00
-- url     : https://prove2.me/theorems/50ccf42a-4005-4b1d-8136-01aeaf92c6f0
-- title:
--   Actual chain budget with an exact constant atom suffix
-- statement:
--   Let a have n+1 slots. Suppose |O|≤t+1<n+1 and every slot outside O equals c. Let u be the uniform source mean and V its uniform variance. There is one complete actual derivative-root chain with every point z_i=c for i≥t+1 and length at most t√(V/n)+√(tV/n+|u−c|²).
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterAtomBudget.lean, lines 11-65, SHA-256 2f11dee1b32d89ede0f7af9e5928542e6a595ee27f6439c1eb493c71a2cee897. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
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

theorem DerivativeChainClusterAnchor.exact_atom_history_budget (n t : ℕ) (a : Fin (n+1) → ℂ) (c : ℂ)
    (O : Finset (Fin (n+1))) (hcut : t+1 < n+1) (hO : O.card ≤ t+1)
    (hnear : ∀ i, i ∉ O → a i=c) :
    let u := complexCentroid a
    let V := ∑ i, (n+1:ℝ)⁻¹*‖a i-u‖^2
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧
      (∀ i, t+1 ≤ i.val → z i=c) ∧
      chainCost z ≤ (t:ℝ)*Real.sqrt (V/(n:ℝ))+
        Real.sqrt ((t:ℝ)*V/(n:ℝ)+‖u-c‖^2) := by sorry
