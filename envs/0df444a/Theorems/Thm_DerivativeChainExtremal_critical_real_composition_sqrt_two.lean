-- Prove2me | Theorems.Thm_DerivativeChainExtremal_critical_real_composition_sqrt_two
-- name    : DerivativeChainExtremal.critical_real_composition_sqrt_two
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:18:19.110377+00:00
-- url     : https://prove2.me/theorems/4d5d2360-d0e1-4685-94f2-a3db06f6e18b
-- title:
--   Real-rooted F-prime composition gives the square-root-two bound
-- statement:
--   Let p have degree n+1 with n≥1 and roots in B(o,R), R≥0. Suppose k≥2, F is a real polynomial whose derivative splits over ℝ, |σ|=1, A≠0, and p(centroid(p)+σX)=A(F(X^k)+γ), where γ is complex. Then p has a complete actual derivative-root chain from its centroid of length at most √2√(R²−|centroid(p)−o|²).
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalCriticalComposition.lean, lines 14-48, SHA-256 38c6205d0673fabe1f6da1d972ca3e487d92abf6fdb0191c5ff09c8db7c047e4. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

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
set_option maxHeartbeats 1800000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation

theorem DerivativeChainExtremal.critical_real_composition_sqrt_two (p : Polynomial ℂ) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 2 ≤ k) (hdegree : p.natDegree=n+1)
    (F : Polynomial ℝ) (hF : F.derivative.Splits) (σ A γ o : ℂ) (R : ℝ)
    (hσ : ‖σ‖=1) (hA : A ≠ 0)
    (hform : p.comp (C (rootCentroid p)+C σ*X)=C A*(spokePoly k 0 F+C γ))
    (hR : 0 ≤ R) (ha : ∀ w : ℂ, p.eval w=0 → ‖w-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=rootCentroid p ∧
      chainCost z ≤ Real.sqrt 2*Real.sqrt (R^2-‖rootCentroid p-o‖^2) := by sorry
