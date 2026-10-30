-- Prove2me | Theorems.Thm_DerivativeChainPrefixLaws_scaled_sequence_contraction
-- name    : DerivativeChainPrefixLaws.scaled_sequence_contraction
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:32:39.983668+00:00
-- url     : https://prove2.me/theorems/ddc0b632-6b41-4b14-8799-88bc826ccfa8
-- title:
--   Telescoping scaled sequence contraction
-- statement:
--   Let V be any real-valued sequence and h≤n natural numbers. If (k+1)V_k≤kV_(k+1) for every k<n, then nV_h≤hV_n. No nonnegativity hypothesis on V is added.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/RowVariance.lean, lines 87-114, SHA-256 ec1d46d038da9ff7bd8572a9828bbeb2339b62869c766598078d99d8fb79fde6. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared variance prerequisite; the exact owner-frozen formal proof and compiler receipts are the source.

import Mathlib
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

theorem DerivativeChainPrefixLaws.scaled_sequence_contraction (V : ℕ → ℝ) (n h : ℕ) (hh : h ≤ n)
    (hstep : ∀ k<n, (k+1:ℝ)*V k ≤ (k:ℝ)*V (k+1)) :
    (n:ℝ)*V h ≤ (h:ℝ)*V n := by sorry
