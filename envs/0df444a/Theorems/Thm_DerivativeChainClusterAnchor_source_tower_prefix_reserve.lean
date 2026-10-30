-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_source_tower_prefix_reserve
-- name    : DerivativeChainClusterAnchor.source_tower_prefix_reserve
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:51:13.97291+00:00
-- url     : https://prove2.me/theorems/7c21c5bc-ccdd-4fab-8eee-5170197a26c3
-- title:
--   Source-scaled actual polynomial-tower prefix reserve
-- statement:
--   For a uniform polynomial-root tower through row n and h≤n, some h-level prefix history z has length plus terminal distance to c at most h√(V_n/n)+√(hV_n/n+|r₀₀−c|²), where V_n is the uniform variance of row n about its degree-one root. Natural zero indices retain Lean’s total-division convention.
-- source:
--   Previously frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterBudget.lean, lines 12-39, SHA-256 1d385fca9cde10cc53f95d116f42a747aba58943a19a961bdad65fd4c05c926f. Supporting statement retained exactly from the verified archive.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterPrefix
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainPrefixLaws
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.source_tower_prefix_reserve (r : ComplexRootRows) (n h : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (hh : h ≤ n) (c : ℂ) :
    ∃ z : Fin (h+1) → ℂ, IsComplexRowHistory r z ∧
      chainCost z+‖z (Fin.last h)-c‖ ≤
        (h:ℝ)*Real.sqrt (rowCenteredVariance r n (r 0 0)/(n:ℝ))+
          Real.sqrt ((h:ℝ)*rowCenteredVariance r n (r 0 0)/(n:ℝ)+‖r 0 0-c‖^2) := by sorry
