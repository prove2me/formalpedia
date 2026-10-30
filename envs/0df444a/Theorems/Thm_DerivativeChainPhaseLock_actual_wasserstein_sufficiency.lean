-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_actual_wasserstein_sufficiency
-- name    : DerivativeChainPhaseLock.actual_wasserstein_sufficiency
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:50:33.276536+00:00
-- url     : https://prove2.me/theorems/d040c7d2-546c-4593-b76d-c664bbdce231
-- title:
--   A uniform transport budget sufficient for kappa at most sixteen
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $r\in \operatorname{ComplexRootRows}$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(r\!\left(n\right) = a\right)\\
--   &\forall k\in \mathbb N,\quad \bigl(\left(k < n\right)\Longrightarrow \operatorname{UniformPolynomialStep}\!\left(r, k\right)\bigr)\\
--   &\left(\operatorname{towerTransportLength}\!\left(r, n\right) \le \left(\sqrt{15} \, \sqrt{\operatorname{uniformSourceVariance}\!\left(a\right)}\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(\left(\operatorname{kappa}\!\left(a\right) \le \operatorname{uniformComplexTransportRatio}\!\left(a\right)\right) \land \left(\operatorname{uniformComplexTransportRatio}\!\left(a\right) \le 16\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.ComplexRootRows`, `DerivativeChainContinuation.UniformPolynomialStep`, `DerivativeChainContinuation.uniformComplexTransportRatio`, `DerivativeChainPhaseLock.towerTransportLength`, `DerivativeChainPhaseLock.uniformSourceVariance`, `DerivativeChainPrefixLaws.kappa` retain their exact imported definitions. Control the second moment of endpoint costs by the uniform transport length and source variance, then apply the displayed transport budget. The zero-variance source is handled by collapse.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/WassersteinSufficiency.lean, lines 74-94, SHA-256 3b7ca058ac2eb652fff15d783c7e54d45d8aa1b2fa2e4758aba92467d178defd. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
import Definitions.Def_DerivativeChainAnalytic_UniformTransportHistories
import Definitions.Def_DerivativeChainAnalytic_WassersteinSufficiency
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
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

theorem DerivativeChainPhaseLock.actual_wasserstein_sufficiency (n : ℕ) (a : Fin (n+1) → ℂ)
    (r : ComplexRootRows) (htop : r n=a) (hstep : ∀ k<n,UniformPolynomialStep r k)
    (hT : towerTransportLength r n ≤ Real.sqrt 15*Real.sqrt (uniformSourceVariance a)) :
    kappa a ≤ uniformComplexTransportRatio a ∧ uniformComplexTransportRatio a ≤ 16 := by sorry
