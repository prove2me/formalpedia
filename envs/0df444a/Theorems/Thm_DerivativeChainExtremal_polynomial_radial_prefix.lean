-- Prove2me | Theorems.Thm_DerivativeChainExtremal_polynomial_radial_prefix
-- name    : DerivativeChainExtremal.polynomial_radial_prefix
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:10:03.888831+00:00
-- url     : https://prove2.me/theorems/30a07653-f84d-48ca-97b1-6255bc2c438c
-- title:
--   Arbitrary complex polynomial radial-prefix bound
-- statement:
--   Let p have degree n+1, with all actual roots in B(o,R), R≥0. Suppose 1≤m≤n+1, k≥2, r<k, q splits over ℝ, C₀≠0 and |σ|=1. If p^(n+1−m)(centroid(p)+σX)=C₀X^r q(X^k), there is a chain z₀,…,z_n with z_i a root of p^(n−i), z₀=centroid(p), and length at most √(n+2−m)√(R²−|centroid(p)−o|²). Monicity and simplicity are not hypotheses.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalPolynomial.lean, lines 47-85, SHA-256 33b9ab978bad4114e528f812cde88b1c01bddcbe09476391c5ba674957e3e2b2. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

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
set_option maxHeartbeats 2000000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainExtremal.polynomial_radial_prefix (p : Polynomial ℂ)
    (n m k r : ℕ) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ) (σ C₀ o : ℂ) (R : ℝ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (derivative^[n+1-m] p).comp (C (rootCentroid p)+C σ*X)=C C₀*spokePoly k r q)
    (hR : 0 ≤ R) (ha : ∀ w : ℂ, p.eval w=0 → ‖w-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=rootCentroid p ∧
      chainCost z ≤ Real.sqrt (n+1-m+1 : ℕ)*Real.sqrt (R^2-‖rootCentroid p-o‖^2) := by sorry
