-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_majority_atom
-- name    : DerivativeChainClusterAnchor.majority_atom
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T06:00:50.358275+00:00
-- url     : https://prove2.me/theorems/736a1ca1-110a-4f4c-83fb-fab7ff2e810e
-- title:
--   Full monic-polynomial atom bound at two plus square root two
-- statement:
--   Let p be monic of exact natural degree N, with every root occurrence in D(o,R), R≥0. Suppose c is an actual root, r³≤N², and the multiplicity of c is at least N−r using natural subtraction. There is one complete derivative-root selection for p of total length at most (2+√2)R. The actual-root hypothesis implies N>0; r=0, repeated roots, R=0 and small degrees are allowed.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterPolynomial.lean, lines 72-103, SHA-256 c2d11b703110b89e571e83fb606d9fc27e81cf4babb7a2167e1274266ce0f735. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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

theorem DerivativeChainClusterAnchor.majority_atom (p : ℂ[X]) (hp : p.Monic) (n r : ℕ) (hdegree : p.natDegree=n)
    (hcube : r^3 ≤ n^2) (o c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hsource : ∀ z ∈ p.roots, ‖z-o‖ ≤ R) (hc : c ∈ p.roots)
    (hmultiplicity : n-r ≤ p.roots.count c) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      chainCost z ≤ (2+Real.sqrt 2)*R := by sorry
