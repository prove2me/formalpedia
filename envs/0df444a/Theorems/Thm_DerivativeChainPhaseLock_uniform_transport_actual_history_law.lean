-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_uniform_transport_actual_history_law
-- name    : DerivativeChainPhaseLock.uniform_transport_actual_history_law
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:47:44.564157+00:00
-- url     : https://prove2.me/theorems/a5f03b86-72d6-4d9c-92ef-73ff01c5b33a
-- title:
--   Uniform transport actual history law
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $r\in \operatorname{ComplexRootRows}$, $K\colon \prod_{k_{1}\in \mathbb N} \bigl(I_{\left(k_{1} + 1\right)}\longrightarrow \bigl(I_{\left(k_{1} + 2\right)}\longrightarrow \mathbb R\bigr)\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(r\!\left(n\right) = a\right)\\
--   &\forall k\in \mathbb N,\quad \bigl(\left(k < n\right)\Longrightarrow \operatorname{UniformPolynomialStep}\!\left(r, k\right)\bigr)\\
--   &\forall k_{2}\in \mathbb N,\quad \bigl(\left(k_{2} < n\right)\Longrightarrow \operatorname{UniformKernel}\!\left(k_{2}, \left(k_{2} + 1\right), K\!\left(k_{2}\right)\right)\bigr)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \exists κ\in \mathsf{Type},\quad \exists \mathit{inst}\in \operatorname{Fintype}\!\left(κ\right),\quad \exists L\in \operatorname{FiniteBalancedHistoryLaw}\!\left(a, r\!\left(0, 0\right), κ\right),\quad \left(\forall f\in \bigl(\mathbb C\longrightarrow \mathbb R\bigr),\quad \left(\sum_{i\in \mathsf{univ}} \left(\operatorname{weights}\!\left(L, i\right) \, f\!\left(\operatorname{paths}\!\left(L, i, n\right)\right)\right) = \sum_{j\in \mathsf{univ}} \left(\left(\left(n + 1\right)\right)^{-1} \, f\!\left(a\!\left(j\right)\right)\right)\right) \land \left(\sum_{i_{1}\in \mathsf{univ}} \left(\operatorname{weights}\!\left(L, i_{1}\right) \, \operatorname{chainCost}\!\left(\operatorname{paths}\!\left(L, i_{1}\right)\right)\right) = \sum_{k_{3}\in \mathsf{univ}} \operatorname{uniformKernelCost}\!\left(r\!\left(k_{3}\right), r\!\left(\left(k_{3} + 1\right)\right), K\!\left(k_{3}\right)\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.ComplexRootRows`, `DerivativeChainContinuation.UniformPolynomialStep`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.paths`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.weights`, `DerivativeChainPhaseLock.UniformKernel`, `DerivativeChainPhaseLock.uniformKernelCost`, `DerivativeChainPrivate.chainCost` retain their exact imported definitions. Glue the uniform-marginal row kernels into complete labelled histories. Their weights preserve every intermediate marginal and the exact expected edge cost.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/UniformTransportHistories.lean, lines 17-67, SHA-256 e422d33e090f664c9867aa5960ddb557cc08f17cf1e28844cc0e1c8d136f6d2c. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_UniformWasserstein
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
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
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainFiniteHistory
open DerivativeChainPrefixLaws
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.uniform_transport_actual_history_law (n : ℕ) (a : Fin (n+1) → ℂ)
    (r : ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n,UniformPolynomialStep r k)
    (K : (k : ℕ) → Fin (k+1) → Fin (k+2) → ℝ)
    (hK : ∀ k<n,UniformKernel k (k+1) (K k)) :
    ∃ (κ : Type) (inst : Fintype κ),letI := inst;
      ∃ L : FiniteBalancedHistoryLaw a (r 0 0) κ,
        (∀ f : ℂ → ℝ,(∑ i,L.weights i*f (L.paths i (Fin.last n)))=
          ∑ j,(n+1:ℝ)⁻¹*f (a j)) ∧
        (∑ i,L.weights i*chainCost (L.paths i))=
          ∑ k : Fin n,uniformKernelCost (r k.val) (r (k.val+1)) (K k.val) := by sorry
