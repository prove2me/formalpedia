-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_actual_kernel_extension
-- name    : DerivativeChainPhaseLock.actual_kernel_extension
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:46:13.816512+00:00
-- url     : https://prove2.me/theorems/632941d9-4a93-453a-a8ee-1bdc0b4a5134
-- title:
--   Actual kernel extension
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 2\right)}\longrightarrow \mathbb C\bigr)$, $b\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $u\in \mathbb C$, $κ\in \mathsf{Type}$, $\mathit{inst.\_@.BarycentricExtension.1337469049.\_hygCtx.\_hyg.33}\in \operatorname{Fintype}\!\left(κ\right)$, $L\in \operatorname{FiniteBalancedHistoryLaw}\!\left(b, u, κ\right)$, $α\colon \bigl(κ\longrightarrow \bigl(\operatorname{Subtype}\!\left(\bigl(x\in \mathbb C\longmapsto \left(x\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\longrightarrow \mathbb R\bigr)\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(\mathrm D\!\left(\operatorname{fromRoots}\!\left(a\right)\right) = \left(\operatorname{C}\!\left(\left(n + 2\right)\right) \, \operatorname{fromRoots}\!\left(b\right)\right)\right)\\
--   &\forall i\in κ,\quad \forall j\in \operatorname{Subtype}\!\left(\bigl(x_{1}\in \mathbb C\longmapsto \left(x_{1}\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right),\quad \left(0 \le α\!\left(i, j\right)\right)\\
--   &\forall i_{1}\in κ,\quad \left(\sum_{j_{1}\in \mathsf{univ}} α\!\left(i_{1}, j_{1}\right) = 1\right)\\
--   &\forall i_{2}\in κ,\quad \left(\sum_{j_{2}\in \mathsf{univ}} \left(α\!\left(i_{2}, j_{2}\right) \, j_{2}\right) = \operatorname{paths}\!\left(L, i_{2}, n\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \exists M\in \operatorname{FiniteBalancedHistoryLaw}\!\left(a, u, \operatorname{Prod}\!\left(κ, \operatorname{Subtype}\!\left(\bigl(x_{4}\in \mathbb C\longmapsto \left(x_{4}\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\right)\right),\quad \left(\forall \mathit{ij}\in \operatorname{Prod}\!\left(κ, \operatorname{Subtype}\!\left(\bigl(x_{5}\in \mathbb C\longmapsto \left(x_{5}\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\right),\quad \left(\operatorname{weights}\!\left(M, \mathit{ij}\right) = \left(\operatorname{weights}\!\left(L, \operatorname{fst}\!\left(\mathit{ij}\right)\right) \, α\!\left(\operatorname{fst}\!\left(\mathit{ij}\right), \operatorname{snd}\!\left(\mathit{ij}\right)\right)\right)\right) \land \left(\forall \mathit{ij}_{1}\in \operatorname{Prod}\!\left(κ, \operatorname{Subtype}\!\left(\bigl(x_{6}\in \mathbb C\longmapsto \left(x_{6}\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\right),\quad \left(\operatorname{paths}\!\left(M, \mathit{ij}_{1}\right) = \operatorname{snoc}\!\left(\operatorname{paths}\!\left(L, \operatorname{fst}\!\left(\mathit{ij}_{1}\right)\right), \operatorname{snd}\!\left(\mathit{ij}_{1}\right)\right)\right) \land \left(\left(\operatorname{endpointVariance}\!\left(M\right) = \operatorname{parentVariance}\!\left(a, L, α\right)\right) \land \left(\operatorname{meanSquareCost}\!\left(M\right) = \operatorname{parentSquareCost}\!\left(a, L, α\right)\right)\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.endpointVariance`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.meanSquareCost`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.paths`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.weights`, `DerivativeChainPhaseLock.parentSquareCost`, `DerivativeChainPhaseLock.parentVariance`, `DerivativeChainPrivate.fromRoots` retain their exact imported definitions. Append the selected parent-root slot using the given stochastic kernel. Every earlier vertex of each incoming history is retained, and the derivative relation gives actual row membership.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/BarycentricExtension.lean, lines 35-82, SHA-256 7f59754d742fe35968f59280c833a578eefed8b39f01a074d6f24a5fcb780416. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
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
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory DerivativeChainContinuation
universe v
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.actual_kernel_extension {n : ℕ} (a : Fin (n+2) → ℂ) (b : Fin (n+1) → ℂ) (u : ℂ)
    {κ : Type v} [Fintype κ]
    (hderiv : (fromRoots a).derivative=C (n+2:ℂ)*fromRoots b)
    (L : FiniteBalancedHistoryLaw b u κ)
    (α : κ → (fromRoots a).roots.toFinset → ℝ)
    (hα : ∀ i j, 0 ≤ α i j) (hαsum : ∀ i, ∑ j, α i j=1)
    (hαmean : ∀ i, ∑ j, (α i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n)) :
    ∃ M : FiniteBalancedHistoryLaw a u (κ × (fromRoots a).roots.toFinset),
      (∀ ij, M.weights ij=L.weights ij.1*α ij.1 ij.2) ∧
      (∀ ij, M.paths ij=Fin.snoc (L.paths ij.1) (ij.2:ℂ)) ∧
      M.endpointVariance=parentVariance a L α ∧
      M.meanSquareCost=parentSquareCost a L α := by sorry
