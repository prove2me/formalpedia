-- Prove2me | Theorems.Thm_DerivativeChainPrefixLaws_linear_row_root_eq_centroid
-- name    : DerivativeChainPrefixLaws.linear_row_root_eq_centroid
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:17:07.932279+00:00
-- url     : https://prove2.me/theorems/af291f38-4883-4203-943d-97be7e124847
-- title:
--   Linear row root eq centroid
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $v\in \mathbb C$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(\operatorname{row}\!\left(a, 1\right)\!\left(v\right) = 0\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(v = \operatorname{complexCentroid}\!\left(a\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.complexCentroid`, `DerivativeChainPrivate.row` retain their exact imported definitions. Factor the actual source polynomial into root slots and apply the uniform row identities to obtain the stated centroid and variance-controlled tower.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/RowVarianceAdapters.lean, lines 39-52, SHA-256 6b87d4c1da11fa2c9ccefccb13f22e2e861a44d071ac3464a6bbc9ff36817f3d. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainPrefixLaws

theorem DerivativeChainPrefixLaws.linear_row_root_eq_centroid {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ)
    (hv : (row a 1).eval v=0) : v=complexCentroid a := by sorry
