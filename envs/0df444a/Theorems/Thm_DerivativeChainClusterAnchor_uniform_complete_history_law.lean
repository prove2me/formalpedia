-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_uniform_complete_history_law
-- name    : DerivativeChainClusterAnchor.uniform_complete_history_law
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:26:39.976586+00:00
-- url     : https://prove2.me/theorems/907642fe-273e-41b7-8e8c-709c9a04b904
-- title:
--   Finite complete-history law for uniform polynomial root rows
-- statement:
--   For any uniform polynomial-root tower through row h, there is a finite nonnegative probability law on complete row histories. The terminal row index is exactly uniform, the weighted terminal point equals the unique degree-one root r₀₀, and the expected sum of squared increments equals the expected squared terminal displacement from r₀₀.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterUniformHistory.lean, lines 12-93, SHA-256 673fa75080f4a142e676696d9b0351ac717677ea918273a83922a0f385143d4f. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
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
open DerivativeChainContinuation
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.uniform_complete_history_law (r : ComplexRootRows) (h : ℕ)
    (hstep : ∀ k<h, UniformPolynomialStep r k) :
    ∃ (κ : Type) (inst : Fintype κ), letI := inst;
      ∃ (w : κ → ℝ) (z : κ → ℕ → ℂ) (last : κ → Fin (h+1)),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
        (∀ i, z i h=r h (last i)) ∧
        (∀ i k, k ≤ h → ∃ j : Fin (k+1), z i k=r k j) ∧
        (∀ f : Fin (h+1) → ℝ, (∑ i, w i*f (last i))=∑ j, (h+1:ℝ)⁻¹*f j) ∧
        (∑ i, (w i:ℂ)*z i h)=r 0 0 ∧
        (∑ i, w i*historyEnergy h (z i))=(∑ i, w i*‖z i h-r 0 0‖^2) := by sorry
