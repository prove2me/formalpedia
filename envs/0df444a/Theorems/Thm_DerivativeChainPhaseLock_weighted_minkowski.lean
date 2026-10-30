-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_weighted_minkowski
-- name    : DerivativeChainPhaseLock.weighted_minkowski
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:45:52.145642+00:00
-- url     : https://prove2.me/theorems/9c5730e7-28bf-497e-b684-dd7e8e1a3f50
-- title:
--   Weighted minkowski
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $ι\in \mathsf{Type}$, $\mathit{inst.\_@.BarycentricMoments.4006599727.\_hygCtx.\_hyg.3}\in \operatorname{Fintype}\!\left(ι\right)$, $w\colon \bigl(ι\longrightarrow \mathbb R\bigr)$, $A\colon \bigl(ι\longrightarrow \mathbb R\bigr)$, $B\colon \bigl(ι\longrightarrow \mathbb R\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\forall i\in ι,\quad \left(0 \le w\!\left(i\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(\sqrt{\sum_{i_{1}\in \mathsf{univ}} \left(w\!\left(i_{1}\right) \, \left(\left(A\!\left(i_{1}\right) + B\!\left(i_{1}\right)\right)\right)^{2}\right)} \le \left(\sqrt{\sum_{i_{2}\in \mathsf{univ}} \left(w\!\left(i_{2}\right) \, \left(A\!\left(i_{2}\right)\right)^{2}\right)} + \sqrt{\sum_{i_{3}\in \mathsf{univ}} \left(w\!\left(i_{3}\right) \, \left(B\!\left(i_{3}\right)\right)^{2}\right)}\right)\right)
--   $$
--
--   Use the conditional barycenter identity to compute the exact edge-energy gain. Weighted Minkowski then bounds the root-mean-square cost after extension.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/BarycentricMoments.lean, lines 48-82, SHA-256 5d92ab8efc8f34b8409a881fc6d74d1443d21307225d5ba5ba3f4088ce963aaf. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
universe v
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.weighted_minkowski {ι : Type v} [Fintype ι] (w A B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    Real.sqrt (∑ i,w i*(A i+B i)^2) ≤
      Real.sqrt (∑ i,w i*(A i)^2)+Real.sqrt (∑ i,w i*(B i)^2) := by sorry
