-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_uniform_kernel_minimum
-- name    : DerivativeChainPhaseLock.uniform_kernel_minimum
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:47:37.625526+00:00
-- url     : https://prove2.me/theorems/c3d9fbbe-3caa-46f7-a6d4-8cff9e478658
-- title:
--   Uniform kernel minimum
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $m\in \mathbb N$, $n\in \mathbb N$, $x\colon \bigl(I_{\left(m + 1\right)}\longrightarrow \mathbb C\bigr)$, $y\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$. Then
--
--   $$
--   \exists K\colon \bigl(I_{\left(m + 1\right)}\longrightarrow \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb R\bigr)\bigr),\quad \left(\operatorname{UniformKernel}\!\left(m, n, K\right) \land \forall Q\in \bigl(I_{\left(m + 1\right)}\longrightarrow \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb R\bigr)\bigr),\quad \bigl(\operatorname{UniformKernel}\!\left(m, n, Q\right)\Longrightarrow \left(\operatorname{uniformKernelCost}\!\left(x, y, K\right) \le \operatorname{uniformKernelCost}\!\left(x, y, Q\right)\right)\bigr)\right)
--   $$
--
--   The named functions `DerivativeChainPhaseLock.UniformKernel`, `DerivativeChainPhaseLock.uniformKernelCost` retain their exact imported definitions. Use the compact finite stochastic-kernel feasible set and continuity of its linear transport cost to attain the minimum; nonnegative costs give its sign.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/UniformWasserstein.lean, lines 24-73, SHA-256 d2b3a395a27d92bbd7b053e89aa3da51910edc46c26e0351e65151d2b5b8fe4b. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_UniformWasserstein
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
open DerivativeChainPrefixLaws
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.uniform_kernel_minimum {m n : ℕ} (x : Fin (m+1) → ℂ) (y : Fin (n+1) → ℂ) :
    ∃ K : Fin (m+1) → Fin (n+1) → ℝ,UniformKernel m n K ∧
      ∀ Q,UniformKernel m n Q → uniformKernelCost x y K ≤ uniformKernelCost x y Q := by sorry
