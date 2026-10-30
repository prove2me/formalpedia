-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_below_sixteen_polynomial
-- name    : DerivativeChainClusterAnchor.below_sixteen_polynomial
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:03:59.409065+00:00
-- url     : https://prove2.me/theorems/b8248fe4-a4db-4cad-a529-b1b6384fe29a
-- title:
--   Actual monic complete-chain bound below degree sixteen
-- statement:
--   Let p be monic of exact degree 0<N<16, with all actual roots in D(o,R) and R≥0. One complete derivative-root selection has length at most √(N−1)R and, when R>0, length strictly below 4R.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterPolynomial.lean, lines 134-148, SHA-256 c2d11b703110b89e571e83fb606d9fc27e81cf4babb7a2167e1274266ce0f735. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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

theorem DerivativeChainClusterAnchor.below_sixteen_polynomial (p : ℂ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree=n) (hn : 0 < n) (hsmall : n < 16)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hsource : ∀ z ∈ p.roots, ‖z-o‖ ≤ R) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      chainCost z ≤ Real.sqrt ((n-1:ℕ):ℝ)*R ∧ (0 < R → chainCost z < 4*R) := by sorry
