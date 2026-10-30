-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_iterate_derivative_slot_product
-- name    : DerivativeChainClusterAnchor.iterate_derivative_slot_product
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:10:46.173318+00:00
-- url     : https://prove2.me/theorems/3f3f4beb-4b05-4925-a3ba-c24965afd6ac
-- title:
--   Iterated derivative expansion with repeated root slots
-- statement:
--   Let S be a finite set of distinct slot indices, let a assign any complex value to each slot, and let k≤|S|. The k-th derivative of ∏ᵢ∈S(X−aᵢ) equals k! times the sum of ∏ᵢ∈T(X−aᵢ) over all subsets T⊆S of size |S|−k. Equal root values in different slots are permitted.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSubsetProduct.lean, lines 11-48, SHA-256 a6d05e4fa5d192091e249eddae712315f75cec01915ba331061f322bcc396ae6. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

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
open Polynomial Finset
open DerivativeChainClusterAnchor


-- Slot indices retain coincident root values as separate factors.
-- The proof extends Mathlib's iterate_derivative_prod_X_sub_C to a noninjective root map.

theorem DerivativeChainClusterAnchor.iterate_derivative_slot_product {ι : Type} [DecidableEq ι]
    (a : ι → ℂ) {S : Finset ι} {k : ℕ} (hk : k ≤ S.card) :
    derivative^[k] (∏ i ∈ S, (X-C (a i))) =
      (k.factorial : ℂ[X]) * ∑ T ∈ S.powersetCard (S.card-k), ∏ i ∈ T, (X-C (a i)) := by sorry
