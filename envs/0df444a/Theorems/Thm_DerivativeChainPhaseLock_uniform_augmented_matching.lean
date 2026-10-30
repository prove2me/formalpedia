-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_uniform_augmented_matching
-- name    : DerivativeChainPhaseLock.uniform_augmented_matching
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:18:45.651993+00:00
-- url     : https://prove2.me/theorems/1ab1cdad-2f66-49b9-8a71-69cb6412da74
-- title:
--   Uniform augmented matching
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $r\in \operatorname{ComplexRootRows}$, $k\in \mathbb N$. Assume
--
--   $$
--   \begin{aligned}
--   &\operatorname{UniformPolynomialStep}\!\left(r, k\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \exists σ\in \operatorname{Perm}\!\left(I_{\left(k + 2\right)}\right),\quad \left(\sum_{i\in \mathsf{univ}} \left(\left\|\left(r\!\left(\left(k + 1\right), σ\!\left(i\right)\right) - \operatorname{snoc}\!\left(r\!\left(k\right), \operatorname{complexCentroid}\!\left(r\!\left(\left(k + 1\right)\right)\right), i\right)\right)\right\|\right)^{2} \le \left(\sum_{j\in \mathsf{univ}} \left(\left\|\left(r\!\left(\left(k + 1\right), j\right) - \operatorname{complexCentroid}\!\left(r\!\left(\left(k + 1\right)\right)\right)\right)\right\|\right)^{2} - \sum_{i_{1}\in \mathsf{univ}} \left(\left\|\left(r\!\left(k, i_{1}\right) - \operatorname{complexCentroid}\!\left(r\!\left(\left(k + 1\right)\right)\right)\right)\right\|\right)^{2}\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.ComplexRootRows`, `DerivativeChainContinuation.UniformPolynomialStep`, `DerivativeChainContinuation.complexCentroid` retain their exact imported definitions. Pad the derivative-root kernel by the centroid row to obtain a doubly stochastic matrix. The finite variance identity computes its cost, and permutation selection supplies the matching.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/AugmentedMatching.lean, lines 26-82, SHA-256 5143e9e369bfb29da654ef7e676f642d616c5ae7409a6a0f1c3f9492592ae9ee. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial Matrix DerivativeChainContinuation
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.uniform_augmented_matching (r : ComplexRootRows) (k : ℕ)
    (hstep : UniformPolynomialStep r k) :
    ∃ σ : Equiv.Perm (Fin (k+2)),
      (∑ i,‖r (k+1) (σ i)-(Fin.snoc (r k) (complexCentroid (r (k+1))) : Fin (k+2) → ℂ) i‖^2) ≤
      (∑ j,‖r (k+1) j-complexCentroid (r (k+1))‖^2)-
      (∑ i,‖r k i-complexCentroid (r (k+1))‖^2) := by sorry
