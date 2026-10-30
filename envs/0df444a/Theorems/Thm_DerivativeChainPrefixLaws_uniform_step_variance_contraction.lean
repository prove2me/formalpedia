-- Prove2me | Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_variance_contraction
-- name    : DerivativeChainPrefixLaws.uniform_step_variance_contraction
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:37:47.522809+00:00
-- url     : https://prove2.me/theorems/53ca6158-d8db-4621-a1e0-5d056866a513
-- title:
--   Exact-index variance contraction for a uniform polynomial step
-- statement:
--   For a UniformPolynomialStep from row k+1 to row k, if the larger-row centroid is u, then (k+1) times the uniform second moment of the smaller row about u is at most k times that of the larger row.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/RowVariance.lean, lines 63-85, SHA-256 ec1d46d038da9ff7bd8572a9828bbeb2339b62869c766598078d99d8fb79fde6. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared variance prerequisite; the exact owner-frozen formal proof and compiler receipts are the source.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
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
open Polynomial DerivativeChainContinuation
open DerivativeChainPrefixLaws

theorem DerivativeChainPrefixLaws.uniform_step_variance_contraction (r : ComplexRootRows) (k : ℕ)
    (hstep : UniformPolynomialStep r k) (u : ℂ)
    (hc : complexCentroid (r (k+1))=u) :
    (k+1:ℝ)*secondMoment (fun j : Fin (k+1) => r k j-u) ≤
      (k:ℝ)*secondMoment (fun i : Fin (k+2) => r (k+1) i-u) := by sorry
