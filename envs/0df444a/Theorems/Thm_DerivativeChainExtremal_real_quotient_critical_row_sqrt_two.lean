-- Prove2me | Theorems.Thm_DerivativeChainExtremal_real_quotient_critical_row_sqrt_two
-- name    : DerivativeChainExtremal.real_quotient_critical_row_sqrt_two
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:16:32.539056+00:00
-- url     : https://prove2.me/theorems/a4be7f7c-dfbb-4181-b8e0-25e4f9e62224
-- title:
--   Real-rooted spoke critical row gives the square-root-two disk bound
-- statement:
--   Let p have degree n+1 with n≥1 and all roots in B(o,R), R≥0. Suppose, after the centroid translation and a unit rotation, p′ is a nonzero scalar times X^r q(X^k), where k≥2, r<k and q splits over ℝ. Then some complete actual derivative-root chain starts at the centroid and has length at most √2√(R²−|centroid(p)−o|²).
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalCorollaries.lean, lines 47-60, SHA-256 fd8b984a214beded28d95deac44fedea05764273f50fa4c8b175b1e7a68bb270. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

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

theorem DerivativeChainExtremal.real_quotient_critical_row_sqrt_two (p : Polynomial ℂ)
    (n k r : ℕ) (hn : 1 ≤ n) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ)
    (σ C₀ o : ℂ) (R : ℝ) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : p.derivative.comp (C (rootCentroid p)+C σ*X)=C C₀*spokePoly k r q)
    (hR : 0 ≤ R) (ha : ∀ w : ℂ, p.eval w=0 → ‖w-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=rootCentroid p ∧
      chainCost z ≤ Real.sqrt 2*Real.sqrt (R^2-‖rootCentroid p-o‖^2) := by sorry
