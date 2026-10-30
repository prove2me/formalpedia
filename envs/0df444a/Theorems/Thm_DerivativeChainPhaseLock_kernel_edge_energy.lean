-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_kernel_edge_energy
-- name    : DerivativeChainPhaseLock.kernel_edge_energy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:46:28.150776+00:00
-- url     : https://prove2.me/theorems/dee5fa29-4c03-43f4-b85b-a8b0f61ca43c
-- title:
--   Kernel edge energy
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 2\right)}\longrightarrow \mathbb C\bigr)$, $b\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $u\in \mathbb C$, $κ\in \mathsf{Type}$, $\mathit{inst.\_@.BarycentricMoments.2257845342.\_hygCtx.\_hyg.33}\in \operatorname{Fintype}\!\left(κ\right)$, $L\in \operatorname{FiniteBalancedHistoryLaw}\!\left(b, u, κ\right)$, $α\colon \bigl(κ\longrightarrow \bigl(\operatorname{Subtype}\!\left(\bigl(x\in \mathbb C\longmapsto \left(x\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\longrightarrow \mathbb R\bigr)\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\forall i\in κ,\quad \left(\sum_{j\in \mathsf{univ}} α\!\left(i, j\right) = 1\right)\\
--   &\forall i_{1}\in κ,\quad \left(\sum_{j_{1}\in \mathsf{univ}} \left(α\!\left(i_{1}, j_{1}\right) \, j_{1}\right) = \operatorname{paths}\!\left(L, i_{1}, n\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(\operatorname{edgeSquareEnergy}\!\left(a, L, α\right) = \left(\operatorname{parentVariance}\!\left(a, L, α\right) - \operatorname{endpointVariance}\!\left(L\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.endpointVariance`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.paths`, `DerivativeChainPhaseLock.edgeSquareEnergy`, `DerivativeChainPhaseLock.parentVariance`, `DerivativeChainPrivate.fromRoots` retain their exact imported definitions. Use the conditional barycenter identity to compute the exact edge-energy gain. Weighted Minkowski then bounds the root-mean-square cost after extension.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/BarycentricMoments.lean, lines 26-46, SHA-256 5d92ab8efc8f34b8409a881fc6d74d1443d21307225d5ba5ba3f4088ce963aaf. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_BarycentricMoments
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

theorem DerivativeChainPhaseLock.kernel_edge_energy {n : ℕ} (a : Fin (n+2) → ℂ)
    {b : Fin (n+1) → ℂ} {u : ℂ} {κ : Type v} [Fintype κ]
    (L : FiniteBalancedHistoryLaw b u κ) (α : κ → (fromRoots a).roots.toFinset → ℝ)
    (hαsum : ∀ i, ∑ j, α i j=1)
    (hαmean : ∀ i, ∑ j, (α i j:ℂ)*(j:ℂ)=L.paths i (Fin.last n)) :
    edgeSquareEnergy a L α=parentVariance a L α-L.endpointVariance := by sorry
