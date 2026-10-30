-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_birkhoff_cost_selection
-- name    : DerivativeChainPhaseLock.birkhoff_cost_selection
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:16:55.630457+00:00
-- url     : https://prove2.me/theorems/fec87866-5b74-4481-8380-29b418daaf70
-- title:
--   Birkhoff cost selection
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $ι\in \mathsf{Type}$, $\mathit{inst.\_@.BirkhoffCostSelection.2067094565.\_hygCtx.\_hyg.3}\in \operatorname{Fintype}\!\left(ι\right)$, $\mathit{inst.\_@.BirkhoffCostSelection.2067094565.\_hygCtx.\_hyg.6}\in \operatorname{DecidableEq}\!\left(ι\right)$, $S\in \operatorname{Matrix}\!\left(ι, ι, \mathbb R\right)$, $c\colon \bigl(ι\longrightarrow \bigl(ι\longrightarrow \mathbb R\bigr)\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(S\in \operatorname{doublyStochastic}\!\left(\mathbb R, ι\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \exists σ\in \operatorname{Perm}\!\left(ι\right),\quad \left(\sum_{i\in \mathsf{univ}} c\!\left(i, σ\!\left(i\right)\right) \le \sum_{i_{1}\in \mathsf{univ}} \sum_{j\in \mathsf{univ}} \left(S\!\left(i_{1}, j\right) \, c\!\left(i_{1}, j\right)\right)\right)
--   $$
--
--   Decompose the doubly stochastic matrix into a convex combination of permutation matrices. One permutation has cost no larger than the weighted average.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/BirkhoffCostSelection.lean, lines 11-41, SHA-256 a2f6359892d5400364cd29a8958d0d74baaf3997b29ce18a08afbb424f2f813a. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
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
open Matrix
universe v
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.birkhoff_cost_selection {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S ∈ doublyStochastic ℝ ι) (c : ι → ι → ℝ) :
    ∃ σ : Equiv.Perm ι, (∑ i,c i (σ i)) ≤ ∑ i,∑ j,S i j*c i j := by sorry
