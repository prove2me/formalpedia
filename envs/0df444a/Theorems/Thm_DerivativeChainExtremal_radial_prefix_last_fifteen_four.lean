-- Prove2me | Theorems.Thm_DerivativeChainExtremal_radial_prefix_last_fifteen_four
-- name    : DerivativeChainExtremal.radial_prefix_last_fifteen_four
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:14:35.285315+00:00
-- url     : https://prove2.me/theorems/7088c866-533f-4bbd-bb56-a936a2c49663
-- title:
--   A radial prefix followed by at most fifteen derivative levels has a length-four chain
-- statement:
--   Under the actual-polynomial radial-prefix hypotheses with all roots in the closed unit disk, if n+1−m≤15, then some complete derivative-root chain starts at the centroid and has length at most 4.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalCorollaries.lean, lines 31-45, SHA-256 fd8b984a214beded28d95deac44fedea05764273f50fa4c8b175b1e7a68bb270. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
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
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation

theorem DerivativeChainExtremal.radial_prefix_last_fifteen_four (p : Polynomial ℂ)
    (n m k r : ℕ) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ) (σ C₀ : ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (derivative^[n+1-m] p).comp (C (rootCentroid p)+C σ*X)=C C₀*spokePoly k r q)
    (ha : ∀ w : ℂ, p.eval w=0 → ‖w‖ ≤ 1) (hd : n+1-m ≤ 15) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=rootCentroid p ∧ chainCost z ≤ 4 := by sorry
