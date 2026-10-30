-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_actual_polynomial_slots
-- name    : DerivativeChainClusterAnchor.actual_polynomial_slots
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T05:29:55.768044+00:00
-- url     : https://prove2.me/theorems/6eaf964a-aab0-4762-bc5b-ec70c42ff89c
-- title:
--   Actual root-slot enumeration preserving filtered multiplicity
-- statement:
--   For any monic complex polynomial p of exact degree n and any decidable predicate f on complex numbers, there is an indexed list a of n actual roots with p=∏ᵢ(X−aᵢ), every aᵢ in p.roots, and exactly the same number of f-satisfying slots as occurrences in the filtered root multiset. This includes n=0.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterPolynomial.lean, lines 10-26, SHA-256 c2d11b703110b89e571e83fb606d9fc27e81cf4babb7a2167e1274266ce0f735. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/final_cluster/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
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
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor

theorem DerivativeChainClusterAnchor.actual_polynomial_slots (p : ℂ[X]) (hp : p.Monic) (n : ℕ) (hdegree : p.natDegree=n)
    (f : ℂ → Prop) [DecidablePred f] :
    ∃ a : Fin n → ℂ, p=fromRoots a ∧ (∀ i, a i ∈ p.roots) ∧
      ((Finset.univ : Finset (Fin n)).filter (fun i => f (a i))).card=(p.roots.filter f).card := by sorry
