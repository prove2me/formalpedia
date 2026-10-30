-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_all_roots_cluster_polynomial
-- name    : DerivativeChainClusterAnchor.all_roots_cluster_polynomial
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:00:15.495987+00:00
-- url     : https://prove2.me/theorems/3e3075f9-19bb-44da-892f-c4acb893168c
-- title:
--   Complete chain bound for a fully clustered monic polynomial
-- statement:
--   Let p be monic of exact degree N>0 and suppose every actual root lies in D(c,ε), where ε≥0. Then p has a complete actual derivative-root selection with length at most √(N−1)ε.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterPolynomial.lean, lines 105-116, SHA-256 c2d11b703110b89e571e83fb606d9fc27e81cf4babb7a2167e1274266ce0f735. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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

theorem DerivativeChainClusterAnchor.all_roots_cluster_polynomial (p : ℂ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree=n) (hn : 0 < n) (c : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hsource : ∀ z ∈ p.roots, ‖z-c‖ ≤ ε) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      chainCost z ≤ Real.sqrt ((n-1:ℕ):ℝ)*ε := by sorry
