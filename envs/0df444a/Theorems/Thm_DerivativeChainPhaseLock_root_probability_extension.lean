-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_root_probability_extension
-- name    : DerivativeChainPhaseLock.root_probability_extension
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:50:40.717862+00:00
-- url     : https://prove2.me/theorems/c3f41eb4-ae96-45b4-a376-db4ed2296364
-- title:
--   Root probability extension
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 2\right)}\longrightarrow \mathbb C\bigr)$, $b\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $u\in \mathbb C$, $κ\in \mathsf{Type}$, $\mathit{inst.\_@.RootProbabilityExtension.3941136416.\_hygCtx.\_hyg.33}\in \operatorname{Fintype}\!\left(κ\right)$, $L\in \operatorname{FiniteBalancedHistoryLaw}\!\left(b, u, κ\right)$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(\mathrm D\!\left(\operatorname{fromRoots}\!\left(a\right)\right) = \left(\operatorname{C}\!\left(\left(n + 2\right)\right) \, \operatorname{fromRoots}\!\left(b\right)\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \exists M\in \operatorname{FiniteBalancedHistoryLaw}\!\left(a, u, \operatorname{Prod}\!\left(κ, \operatorname{Subtype}\!\left(\bigl(x\in \mathbb C\longmapsto \left(x\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\right)\right),\quad \left(\forall \mathit{ij}\in \operatorname{Prod}\!\left(κ, \operatorname{Subtype}\!\left(\bigl(x_{1}\in \mathbb C\longmapsto \left(x_{1}\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\right),\quad \left(\operatorname{weights}\!\left(M, \mathit{ij}\right) = \left(\operatorname{weights}\!\left(L, \operatorname{fst}\!\left(\mathit{ij}\right)\right) \, \operatorname{rootKernel}\!\left(a, L, \operatorname{fst}\!\left(\mathit{ij}\right), \operatorname{snd}\!\left(\mathit{ij}\right)\right)\right)\right) \land \left(\forall \mathit{ij}_{1}\in \operatorname{Prod}\!\left(κ, \operatorname{Subtype}\!\left(\bigl(x_{2}\in \mathbb C\longmapsto \left(x_{2}\in \operatorname{toFinset}\!\left(\operatorname{roots}\!\left(\operatorname{fromRoots}\!\left(a\right)\right)\right)\right)\bigr)\right)\right),\quad \left(\operatorname{paths}\!\left(M, \mathit{ij}_{1}\right) = \operatorname{snoc}\!\left(\operatorname{paths}\!\left(L, \operatorname{fst}\!\left(\mathit{ij}_{1}\right)\right), \operatorname{snd}\!\left(\mathit{ij}_{1}\right)\right)\right) \land \left(\left(\operatorname{endpointVariance}\!\left(M\right) = \operatorname{parentVariance}\!\left(a, L, \operatorname{rootKernel}\!\left(a, L\right)\right)\right) \land \left(\left(\operatorname{edgeSquareEnergy}\!\left(a, L, \operatorname{rootKernel}\!\left(a, L\right)\right) = \left(\operatorname{endpointVariance}\!\left(M\right) - \operatorname{endpointVariance}\!\left(L\right)\right)\right) \land \left(\sqrt{\operatorname{meanSquareCost}\!\left(M\right)} \le \left(\sqrt{\operatorname{meanSquareCost}\!\left(L\right)} + \sqrt{\left(\operatorname{endpointVariance}\!\left(M\right) - \operatorname{endpointVariance}\!\left(L\right)\right)}\right)\right)\right)\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.endpointVariance`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.meanSquareCost`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.paths`, `DerivativeChainFiniteHistory.FiniteBalancedHistoryLaw.weights`, `DerivativeChainPhaseLock.edgeSquareEnergy`, `DerivativeChainPhaseLock.parentVariance`, `DerivativeChainPhaseLock.rootKernel`, `DerivativeChainPrivate.fromRoots` retain their exact imported definitions. Use the actual Gauss–Lucas root-probability kernel, including its shared-root branch, to instantiate the retained-prefix extension.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/RootProbabilityExtension.lean, lines 26-49, SHA-256 92d0de0dd5da52595a16d6e296fec96efcd94ba9db1b78bac107940cc7800634. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_BarycentricExtension
import Definitions.Def_DerivativeChainAnalytic_BarycentricMoments
import Definitions.Def_DerivativeChainAnalytic_FiniteBalancedHistoryLaw
import Definitions.Def_DerivativeChainAnalytic_RootProbabilityExtension
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
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainFiniteHistory
universe v
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.root_probability_extension {n : ℕ} (a : Fin (n+2) → ℂ) (b : Fin (n+1) → ℂ)
    (u : ℂ) {κ : Type v} [Fintype κ]
    (hderiv : (fromRoots a).derivative=C (n+2:ℂ)*fromRoots b)
    (L : FiniteBalancedHistoryLaw b u κ) :
    ∃ M : FiniteBalancedHistoryLaw a u (κ × (fromRoots a).roots.toFinset),
      (∀ ij,M.weights ij=L.weights ij.1*rootKernel a L ij.1 ij.2) ∧
      (∀ ij,M.paths ij=Fin.snoc (L.paths ij.1) (ij.2:ℂ)) ∧
      M.endpointVariance=parentVariance a L (rootKernel a L) ∧
      edgeSquareEnergy a L (rootKernel a L)=M.endpointVariance-L.endpointVariance ∧
      Real.sqrt M.meanSquareCost ≤ Real.sqrt L.meanSquareCost+
        Real.sqrt (M.endpointVariance-L.endpointVariance) := by sorry
