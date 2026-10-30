-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_sampled_exponential_bound
-- name    : DerivativeChainClusterAnchor.sampled_exponential_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:17:09.193814+00:00
-- url     : https://prove2.me/theorems/ada3dea5-6ae0-4253-98db-01a892a81775
-- title:
--   Exponential moment bound for sampled outliers
-- statement:
--   For n>0, m≤n, t≥0 and a fixed slot set O, the uniform average of (1+t)^|S∩O| over all m-element subsets S is at most (1+(m/n)t)^|O|.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterEnvelope.lean, lines 37-54, SHA-256 7739ee82dcf73732f2fa09786d34b145b0697f515eb9b15ebd9a8bedcce61422. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
open Finset Polynomial
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.sampled_exponential_bound {n : ℕ} (O : Finset (Fin n)) (m : ℕ) (hn : 0 < n)
    (hm : m ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, (1+t)^(S ∩ O).card) /
        (n.choose m:ℝ) ≤ (1+(m:ℝ)/(n:ℝ)*t)^O.card := by sorry
