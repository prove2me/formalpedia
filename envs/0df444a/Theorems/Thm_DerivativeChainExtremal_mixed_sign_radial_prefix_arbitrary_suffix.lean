-- Prove2me | Theorems.Thm_DerivativeChainExtremal_mixed_sign_radial_prefix_arbitrary_suffix
-- name    : DerivativeChainExtremal.mixed_sign_radial_prefix_arbitrary_suffix
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:07:52.259633+00:00
-- url     : https://prove2.me/theorems/6e4550bb-91ec-406c-b6ba-4aa3e4b769c1
-- title:
--   Mixed-sign radial prefix with an arbitrary actual polynomial suffix
-- statement:
--   Let a consist of n+1 source root slots in a disk B(o,R), R≥0. Let 1≤m≤n+1, k≥2 and r<k. Suppose q is real-rooted, C₀≠0 and |σ|=1, and the degree-m ordinary derivative row, after substituting centroid(a)+σX, is C₀X^r q(X^k). Then there is a complete actual derivative-root chain starting at centroid(a), of length at most √(n+2−m)√(R²−|centroid(a)−o|²). No sign restriction on the real roots of q is imposed.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalRealQuotient.lean, lines 55-68, SHA-256 40715da953f9acd802e1fa160b2d17d1cd169a899e5043ab477a59ee4adde14d. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
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
set_option maxHeartbeats 2000000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainExtremal.mixed_sign_radial_prefix_arbitrary_suffix {n : ℕ} (a : Fin (n+1) → ℂ)
    (m k r : ℕ) (q : Polynomial ℝ) (σ C₀ o : ℂ) (R : ℝ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (row a m).comp (C (complexCentroid a)+C σ*X)=C C₀*spokePoly k r q)
    (hR : 0 ≤ R) (ha : ∀ i, ‖a i-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ, IsChain a z ∧ z 0=complexCentroid a ∧
      chainCost z ≤ Real.sqrt (n+1-m+1 : ℕ)*Real.sqrt (R^2-‖complexCentroid a-o‖^2) := by sorry
