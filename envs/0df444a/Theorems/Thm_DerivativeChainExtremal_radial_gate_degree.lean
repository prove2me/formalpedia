-- Prove2me | Theorems.Thm_DerivativeChainExtremal_radial_gate_degree
-- name    : DerivativeChainExtremal.radial_gate_degree
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T01:20:31.640177+00:00
-- url     : https://prove2.me/theorems/ccc1cd02-a820-4c82-a1ec-9e621fb49f94
-- title:
--   The explicit radial example has degree ten
-- statement:
--   The complex polynomial P=3072X¹⁰−1600X⁶+240X²+15i has natural degree ten.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/extremal/snapshots/radial-prefix-v1/ExtremalGateExample.lean, lines 14-16, SHA-256 625f7b8884b39976e87f03458efad9eb0da74d4c2f7ce720384f4b57a033c69c. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/POSITIVE_GATE.md, SHA-256 bb50241b080580c05ffd35958aa8bef210234efbb7d16944d0ace8a8895c0765; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/extremal/source_provenance/RESULT.md, SHA-256 41e540e06897511bc15c8d4c580011f42c3d64e65c1169d46028c9bb9d9c9f60.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ExtremalGateExample
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

theorem DerivativeChainExtremal.radial_gate_degree : radialGateExample.natDegree=10 := by sorry
