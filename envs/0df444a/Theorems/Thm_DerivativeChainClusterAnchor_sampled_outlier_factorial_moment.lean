-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_sampled_outlier_factorial_moment
-- name    : DerivativeChainClusterAnchor.sampled_outlier_factorial_moment
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:15:40.602894+00:00
-- url     : https://prove2.me/theorems/c881b80f-6107-4aa1-932a-76258369f8a3
-- title:
--   Exact factorial moment of sampled outlier slots
-- statement:
--   Choose an m-element subset S uniformly from n indexed slots, with m,j≤n and a fixed outlier set O. The expectation of binomial(|S∩O|,j) equals binomial(|O|,j)·(m)ⱼ/(n)ⱼ, using Lean’s total real division also in degenerate cases.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterFactorialMoments.lean, lines 75-101, SHA-256 aceb4672a9f589ce5bba6ce2c19858a5f99ef1e2d70b1a984da32048d5f6d0eb. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.sampled_outlier_factorial_moment {n : ℕ} (O : Finset (Fin n)) (m j : ℕ)
    (hm : m ≤ n) (hj : j ≤ n) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, ((S ∩ O).card.choose j:ℝ)) /
        (n.choose m:ℝ) =
      (O.card.choose j:ℝ)*(m.descFactorial j:ℝ)/(n.descFactorial j:ℝ) := by sorry
