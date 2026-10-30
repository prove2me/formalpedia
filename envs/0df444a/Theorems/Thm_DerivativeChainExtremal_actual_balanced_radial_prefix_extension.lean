-- Prove2me | Theorems.Thm_DerivativeChainExtremal_actual_balanced_radial_prefix_extension
-- name    : DerivativeChainExtremal.actual_balanced_radial_prefix_extension
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:49:16.525141+00:00
-- url     : https://prove2.me/theorems/1602f615-9e6e-4eba-ac90-8d19f8bf4d3e
-- title:
--   Balanced actual radial prefix extended through an arbitrary suffix
-- statement:
--   Consider n+1 actual source root slots contained in a disk of radius R≥0 about o. Suppose a finite nonnegative probability law of actual derivative-root prefixes of m levels starts at u, ends at a common radius ρ≥0 about u with weighted endpoint mean u, and each prefix has length exactly ρ, where 1≤m≤n+1. Then some complete actual derivative-root chain starts at u and has length at most √(n+2−m)√(R²−|u−o|²).
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalActualSuffix.lean, lines 10-103, SHA-256 83f142d5444efdc382432f90a5a79071d0706097d57b2f0c0e7851b347b031d7. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

import Mathlib
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
set_option maxHeartbeats 2500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainExtremal.actual_balanced_radial_prefix_extension {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) (u o : ℂ) (R ρ : ℝ)
    (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (ha : ∀ i, ‖a i-o‖ ≤ R)
    {ι : Type} [Fintype ι] (π : ι → ℝ) (f : ι → ℕ → ℂ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i=1)
    (hf0 : ∀ i, f i 0=u)
    (hfroot : ∀ i j, j < m → (row a (j+1)).eval (f i j)=0)
    (hfradius : ∀ i, ‖f i (m-1)-u‖=ρ)
    (hfmean : ∑ i, (π i:ℂ)*f i (m-1)=u)
    (hfcost : ∀ i, (∑ j∈Finset.range (m-1), ‖f i (j+1)-f i j‖)=ρ) :
    ∃ z : Fin (n+1) → ℂ, IsChain a z ∧ z 0=u ∧
      chainCost z ≤ Real.sqrt (n+1-m+1 : ℕ)*Real.sqrt (R^2-‖u-o‖^2) := by sorry
