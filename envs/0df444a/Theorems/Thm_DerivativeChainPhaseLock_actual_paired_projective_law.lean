-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_actual_paired_projective_law
-- name    : DerivativeChainPhaseLock.actual_paired_projective_law
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:17:11.660001+00:00
-- url     : https://prove2.me/theorems/91e09245-d9b2-4426-b18f-c7943ef46cd8
-- title:
--   Actual paired projective law
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $x\colon \bigl(\mathbb N\longrightarrow \mathbb C\bigr)$. Assume
--
--   $$
--   \begin{aligned}
--   &\forall j\in \mathbb N,\quad \bigl(\operatorname{Odd}\!\left(j\right)\Longrightarrow \left(\operatorname{appellCoefficients}\!\left(\operatorname{fromRoots}\!\left(a\right), j\right) = 0\right)\bigr)\\
--   &\operatorname{IsChain}\!\left(a, \bigl(i\in I_{\left(n + 1\right)}\longmapsto x\!\left(i\right)\bigr)\right)\\
--   &\left(x\!\left(0\right) = 0\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \exists L\in \operatorname{FiniteBalancedHistoryLaw}\!\left(a, 0, I_{2}\right),\quad \left(\forall i_{1}\in I_{2},\quad \left(\operatorname{weights}\!\left(L, i_{1}\right) = \frac{1}{2}\right) \land \left(\left(\operatorname{paths}\!\left(L, 0\right) = \operatorname{projectiveHistory}\!\left(x, n\right)\right) \land \left(\left(\operatorname{paths}\!\left(L, 1\right) = \bigl(i_{2}\in I_{\left(n + 1\right)}\longmapsto \left(-\operatorname{projectiveHistory}\!\left(x, n, i_{2}\right)\right)\bigr)\right) \land \left(\forall i_{3}\in I_{2},\quad \left(\operatorname{chainCost}\!\left(\operatorname{paths}\!\left(L, i_{3}\right)\right) = \operatorname{projectivePathLength}\!\left(x, n\right)\right) \land \left(\left(\operatorname{endpointVariance}\!\left(L\right) = \left(\left\|x\!\left(n\right)\right\|\right)^{2}\right) \land \left(\operatorname{meanSquareCost}\!\left(L\right) = \left(\operatorname{projectivePathLength}\!\left(x, n\right)\right)^{2}\right)\right)\right)\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.appellCoefficients`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.endpointVariance`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.meanSquareCost`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.paths`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.weights`, `DerivativeChainPhaseLock.projectiveHistory`, `DerivativeChainPhaseLock.projectivePathLength`, `DerivativeChainPrivate.IsChain`, `DerivativeChainPrivate.chainCost`, `DerivativeChainPrivate.fromRoots` retain their exact imported definitions. Orient the projective vertices using the stated symmetry, then pair the resulting actual history with its negative. Equal weights give balance and retain every ordinary-row equation.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/ProjectiveHistories.lean, lines 65-105, SHA-256 d8bed978babcb201b0156f81486332e95189de1f1959868adafc5e0046e25b7a. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_ProjectiveHistories
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
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
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.actual_paired_projective_law {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → appellCoefficients (fromRoots a) j=0)
    (x : ℕ → ℂ) (hx : IsChain a (fun i => x i.val)) (hx0 : x 0=0) :
    ∃ L : FiniteBalancedHistoryLaw a 0 (Fin 2),
      (∀ i,L.weights i=1/2) ∧ L.paths 0=projectiveHistory x n ∧
      L.paths 1=(fun i => -projectiveHistory x n i) ∧
      (∀ i,chainCost (L.paths i)=projectivePathLength x n) ∧
      L.endpointVariance=‖x n‖^2 ∧ L.meanSquareCost=(projectivePathLength x n)^2 := by sorry
