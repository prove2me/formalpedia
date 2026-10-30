-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_actual_endpoint_cost_lipschitz
-- name    : DerivativeChainPhaseLock.actual_endpoint_cost_lipschitz
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:46:15.953542+00:00
-- url     : https://prove2.me/theorems/f051fd4f-34cb-4a93-b4c4-fc9844407602
-- title:
--   Actual endpoint cost lipschitz
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $i\in I_{\left(n + 1\right)}$, $j\in I_{\left(n + 1\right)}$. Then
--
--   $$
--   \left(\left|\left(\operatorname{complexEndpointCost}\!\left(a, a\!\left(i\right)\right) - \operatorname{complexEndpointCost}\!\left(a, a\!\left(j\right)\right)\right)\right| \le \left\|\left(a\!\left(i\right) - a\!\left(j\right)\right)\right\|\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.complexEndpointCost` retain their exact imported definitions. Replace the source endpoint while retaining every earlier root of the actual chain. The triangle inequality compares the two endpoint costs.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/ActualEndpointLipschitz.lean, lines 22-61, SHA-256 93b96ab06f07a3c3534e1b5421e4c09dc38cc439ca911a34fa9b70d464715c4a. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
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
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainPrefixLaws
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.actual_endpoint_cost_lipschitz {n : ℕ} (a : Fin (n+1) → ℂ)
    (i j : Fin (n+1)) :
    |complexEndpointCost a (a i)-complexEndpointCost a (a j)| ≤ ‖a i-a j‖ := by sorry
