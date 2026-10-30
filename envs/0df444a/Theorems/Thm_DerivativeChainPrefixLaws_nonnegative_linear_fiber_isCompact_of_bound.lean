-- Prove2me | Theorems.Thm_DerivativeChainPrefixLaws_nonnegative_linear_fiber_isCompact_of_bound
-- name    : DerivativeChainPrefixLaws.nonnegative_linear_fiber_isCompact_of_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:45:53.529625+00:00
-- url     : https://prove2.me/theorems/848a8345-81c7-4fe9-b8cc-042c0ba74895
-- title:
--   Nonnegative linear fiber is Compact of bound
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $ι\in \mathsf{Type}$, $F\in \mathsf{Type}$, $\mathit{inst.\_@.FiniteProgramMin.1726166663.\_hygCtx.\_hyg.4}\in \operatorname{Fintype}\!\left(ι\right)$, $\mathit{inst.\_@.FiniteProgramMin.1726166663.\_hygCtx.\_hyg.7}\in \operatorname{NormedAddCommGroup}\!\left(F\right)$, $\mathit{inst.\_@.FiniteProgramMin.1726166663.\_hygCtx.\_hyg.10}\in \operatorname{NormedSpace}\!\left(\mathbb R, F\right)$, $A\in \operatorname{LinearMap}\!\left(\operatorname{id}\!\left(\mathbb R\right), \bigl(ι\longrightarrow \mathbb R\bigr), F\right)$, $b\in F$, $B\colon \bigl(ι\longrightarrow \mathbb R\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\forall w\in \bigl(ι\longrightarrow \mathbb R\bigr),\quad \bigl(\forall i\in ι,\quad \left(0 \le w\!\left(i\right)\right)\Longrightarrow \bigl(\left(A\!\left(w\right) = b\right)\Longrightarrow \forall i_{1}\in ι,\quad \left(w\!\left(i_{1}\right) \le B\!\left(i_{1}\right)\right)\bigr)\bigr)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \operatorname{IsCompact}\!\left(\operatorname{ofPred}\!\left(\bigl(w_{1}\in \bigl(ι\longrightarrow \mathbb R\bigr)\longmapsto \left(\forall i_{2}\in ι,\quad \left(0 \le w_{1}\!\left(i_{2}\right)\right) \land \left(A\!\left(w_{1}\right) = b\right)\right)\bigr)\right)\right)
--   $$
--
--   Bound every coordinate in the nonnegative feasible fiber, obtain compactness, and minimize the continuous linear objective. The probability constraint supplies the coordinate bound in its special case.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/FiniteProgramMin.lean, lines 9-26, SHA-256 a13eb35a768e6292de8f66f375d86abbae8da6520a2d846017ed48caec9d619f. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
open DerivativeChainPrefixLaws

theorem DerivativeChainPrefixLaws.nonnegative_linear_fiber_isCompact_of_bound {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : (ι → ℝ) →ₗ[ℝ] F) (b : F) (B : ι → ℝ)
    (hbound : ∀ w : ι → ℝ,(∀ i,0 ≤ w i) → A w=b → ∀ i,w i ≤ B i) :
    IsCompact {w : ι → ℝ | (∀ i,0 ≤ w i) ∧ A w=b} := by sorry
