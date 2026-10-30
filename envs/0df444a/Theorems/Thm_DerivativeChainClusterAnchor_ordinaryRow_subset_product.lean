-- Prove2me | Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_subset_product
-- name    : DerivativeChainClusterAnchor.ordinaryRow_subset_product
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:12:32.197423+00:00
-- url     : https://prove2.me/theorems/e080ddd4-dcbf-4e62-a1eb-8ff12d66b6b3
-- title:
--   Normalized derivative row as a uniform subset average
-- statement:
--   For n root slots a and m≤n, the monic normalized derivative Qₘ is the reciprocal of binomial(n,m) times the sum of ∏ᵢ∈S(X−aᵢ) over all m-element subsets of the slot indices.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cluster_anchor/ClusterSubsetProduct.lean, lines 56-69, SHA-256 a6d05e4fa5d192091e249eddae712315f75cec01915ba331061f322bcc396ae6. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Mathematical source checkpoint f6f9312a25cdfb1cc2c359eb04374ae01c451978: /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/PROOF.md, SHA-256 58372fc49757644245d40862747bcba5a45990d6e2d3140f51b913629a2090df; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/RESULT.md, SHA-256 32d429f3fdcc4e6ef33dbd5eeaa34d57ae0e0befad59d01cc01bee0cc1a90b9c; /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/platform/new_analytic/analytic_sources/cluster/source_provenance/VERIFICATION.md, SHA-256 29d6e418d33b3a3eae2f5ac59bc979c87b90e4288066c4a24705670ed682386a.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
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

theorem DerivativeChainClusterAnchor.ordinaryRow_subset_product {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    ordinaryRow a m = C ((n.choose m:ℂ)⁻¹) *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, ∏ i ∈ S, (X-C (a i)) := by sorry
