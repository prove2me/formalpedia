-- Prove2me | Theorems.Thm_DerivativeChainPrefixLaws_history_law_endpoint_weights
-- name    : DerivativeChainPrefixLaws.history_law_endpoint_weights
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:46:06.239992+00:00
-- url     : https://prove2.me/theorems/c1a5ccc6-00e3-447c-8a8a-e075b1768de0
-- title:
--   History law endpoint weights
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $u\in \mathbb C$, $κ\in \mathsf{Type}$, $\mathit{inst.\_@.KappaHistoryBridge.3728446687.\_hygCtx.\_hyg.21}\in \operatorname{Fintype}\!\left(κ\right)$, $L\in \operatorname{FiniteBalancedHistoryLaw}\!\left(a, u, κ\right)$. Then
--
--   $$
--   \exists W\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb R\bigr),\quad \left(\operatorname{BalancedWeights}\!\left(a, \operatorname{complexCentroid}\!\left(a\right), W\right) \land \left(\left(\operatorname{rootLawVariance}\!\left(a, W\right) = \operatorname{endpointVariance}\!\left(L\right)\right) \land \left(\operatorname{rootLawSquareCost}\!\left(a, W\right) \le \operatorname{meanSquareCost}\!\left(L\right)\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.complexCentroid`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.endpointVariance`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.meanSquareCost`, `DerivativeChainPrefixLaws.BalancedWeights`, `DerivativeChainPrefixLaws.rootLawSquareCost`, `DerivativeChainPrefixLaws.rootLawVariance` retain their exact imported definitions. Combine weights of histories sharing an endpoint and compare their costs with the actual endpoint minima. This gives a balanced endpoint law with no larger square-cost budget.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/KappaHistoryBridge.lean, lines 21-84, SHA-256 9ab7a13f96cd4a7f1a6ba1b0af8e5398563cae210951f2444d2d3c4a99e1a0ff. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
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
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
open DerivativeChainPrefixLaws

theorem DerivativeChainPrefixLaws.history_law_endpoint_weights {n : ℕ} {a : Fin (n+1) → ℂ} {u : ℂ}
    {κ : Type v} [Fintype κ] (L : FiniteBalancedHistoryLaw a u κ) :
    ∃ W : Fin (n+1) → ℝ, BalancedWeights a (complexCentroid a) W ∧
      rootLawVariance a W=L.endpointVariance ∧ rootLawSquareCost a W ≤ L.meanSquareCost := by sorry
