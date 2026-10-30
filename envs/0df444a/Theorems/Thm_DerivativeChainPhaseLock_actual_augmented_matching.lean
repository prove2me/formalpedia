-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_actual_augmented_matching
-- name    : DerivativeChainPhaseLock.actual_augmented_matching
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:21:32.725219+00:00
-- url     : https://prove2.me/theorems/5fd88f22-bb7d-4f25-8cce-7badf8e6dfb9
-- title:
--   Matching a source row to its derivative roots and centroid
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 2\right)}\longrightarrow \mathbb C\bigr)$. Then
--
--   $$
--   \exists b\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr),\quad \left(\left(\mathrm D\!\left(\operatorname{fromRoots}\!\left(a\right)\right) = \left(\operatorname{C}\!\left(\left(n + 2\right)\right) \, \operatorname{fromRoots}\!\left(b\right)\right)\right) \land \left(\left(\operatorname{complexCentroid}\!\left(b\right) = \operatorname{complexCentroid}\!\left(a\right)\right) \land \exists σ\in \operatorname{Perm}\!\left(I_{\left(n + 2\right)}\right),\quad \left(\sum_{i\in \mathsf{univ}} \left(\left\|\left(a\!\left(σ\!\left(i\right)\right) - \operatorname{snoc}\!\left(b, \operatorname{complexCentroid}\!\left(a\right), i\right)\right)\right\|\right)^{2} \le \left(\sum_{j\in \mathsf{univ}} \left(\left\|\left(a\!\left(j\right) - \operatorname{complexCentroid}\!\left(a\right)\right)\right\|\right)^{2} - \sum_{i_{1}\in \mathsf{univ}} \left(\left\|\left(b\!\left(i_{1}\right) - \operatorname{complexCentroid}\!\left(a\right)\right)\right\|\right)^{2}\right)\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.complexCentroid`, `DerivativeChainPrivate.fromRoots` retain their exact imported definitions. Pad the derivative-root kernel by the centroid row to obtain a doubly stochastic matrix. The finite variance identity computes its cost, and permutation selection supplies the matching.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/AugmentedMatching.lean, lines 84-97, SHA-256 5143e9e369bfb29da654ef7e676f642d616c5ae7409a6a0f1c3f9492592ae9ee. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_foundations
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

theorem DerivativeChainPhaseLock.actual_augmented_matching (n : ℕ) (a : Fin (n+2) → ℂ) :
    ∃ b : Fin (n+1) → ℂ,
      (DerivativeChainPrivate.fromRoots a).derivative=
        C (n+2:ℂ)*DerivativeChainPrivate.fromRoots b ∧
      complexCentroid b=complexCentroid a ∧
      ∃ σ : Equiv.Perm (Fin (n+2)),
        (∑ i,‖a (σ i)-(Fin.snoc b (complexCentroid a) : Fin (n+2) → ℂ) i‖^2) ≤
          (∑ j,‖a j-complexCentroid a‖^2)-(∑ i,‖b i-complexCentroid a‖^2) := by sorry
