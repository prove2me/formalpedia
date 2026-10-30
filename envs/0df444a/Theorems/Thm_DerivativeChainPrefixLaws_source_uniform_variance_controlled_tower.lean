-- Prove2me | Theorems.Thm_DerivativeChainPrefixLaws_source_uniform_variance_controlled_tower
-- name    : DerivativeChainPrefixLaws.source_uniform_variance_controlled_tower
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:46:11.777692+00:00
-- url     : https://prove2.me/theorems/f4c36818-6eb2-41eb-b8cb-182b5fbde66b
-- title:
--   Actual root-slot tower with source-scaled variance control
-- statement:
--   For every list a of n+1 complex root slots, there is a uniform polynomial-root tower whose top row is exactly a and whose degree-one row is the source centroid. At every h≤n, its variance about that centroid is at most (h/n) times the source variance, with Lean’s total division at n=0.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/RowVarianceAdapters.lean, lines 27-37, SHA-256 6b87d4c1da11fa2c9ccefccb13f22e2e861a44d071ac3464a6bbc9ff36817f3d. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared variance prerequisite; the exact owner-frozen formal proof and compiler receipts are the source.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
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
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainPrefixLaws

theorem DerivativeChainPrefixLaws.source_uniform_variance_controlled_tower (n : ℕ) (a : Fin (n+1) → ℂ) :
    ∃ r : ComplexRootRows, r n=a ∧ (∀ k<n, UniformPolynomialStep r k) ∧
      r 0 0=complexCentroid a ∧
      ∀ h≤n, (∑ j : Fin (h+1), (h+1:ℝ)⁻¹*‖r h j-complexCentroid a‖^2) ≤
        (h:ℝ)/(n:ℝ)*(∑ j : Fin (n+1), (n+1:ℝ)⁻¹*‖a j-complexCentroid a‖^2) := by sorry
