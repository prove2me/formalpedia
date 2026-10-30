-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_source_cluster_tail_bound_full
-- name    : DerivativeChainClusterAnchor.source_cluster_tail_bound_full
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:25:23.899561+00:00
-- url     : https://prove2.me/theorems/d0d3148c-1a41-4348-8867-4a67a99cfbb5
-- title:
--   Full cluster anchor-tail bound without ε≤D
-- statement:
--   Let a have n complex root slots, r>0, 2r<n and |O|≤r. Suppose ε≥0, |aᵢ−c|≤ε outside O, and |aᵢ−c|≤D for every slot. Then Σₘ₌₂ᵣ₊₁ⁿ |Qₘ(c)|^(1/m) ≤ 2nε+8r^(3/2)√(Dε/n). No hypothesis ε≤D is imposed.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSourceAComplete.lean, lines 6-23, SHA-256 e0e2968366bbb449f993c40bd42d7d24dd9fae748d0e8c4267ac7438147c2ef5. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterTail
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
open scoped BigOperators
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.source_cluster_tail_bound_full {n r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hr : 0 < r) (hcut : 2*r < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D) :
    (∑ m ∈ Finset.Icc (2*r+1) n, anchorRadius a c m) ≤
      2*(n:ℝ)*ε+8*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (D*ε/(n:ℝ)) := by sorry
