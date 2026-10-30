-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_actual_paired_radial_kappa
-- name    : DerivativeChainPhaseLock.actual_paired_radial_kappa
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:48:21.334845+00:00
-- url     : https://prove2.me/theorems/2d910ecf-0eef-41ff-90e8-2de66a7de96b
-- title:
--   Kappa bound from paired actual radial histories
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $n\in \mathbb N$, $a\colon \bigl(I_{\left(n + 1\right)}\longrightarrow \mathbb C\bigr)$, $x\colon \bigl(\mathbb N\longrightarrow \mathbb C\bigr)$, $K\in \mathbb R$. Assume
--
--   $$
--   \begin{aligned}
--   &\forall j\in \mathbb N,\quad \bigl(\operatorname{Odd}\!\left(j\right)\Longrightarrow \left(\operatorname{appellCoefficients}\!\left(\operatorname{fromRoots}\!\left(a\right), j\right) = 0\right)\bigr)\\
--   &\operatorname{IsChain}\!\left(a, \bigl(i\in I_{\left(n + 1\right)}\longmapsto x\!\left(i\right)\bigr)\right)\\
--   &\left(x\!\left(0\right) = 0\right)\\
--   &\left(x\!\left(n\right) \ne 0\right)\\
--   &\left(0 \le K\right)\\
--   &\forall k\in \mathbb N,\quad \bigl(\left(k < n\right)\Longrightarrow \left(\left\|x\!\left(k\right)\right\| \le \left\|x\!\left(\left(k + 1\right)\right)\right\|\right)\bigr)\\
--   &\forall k_{1}\in \mathbb N,\quad \bigl(\left(k_{1} < n\right)\Longrightarrow \left(\left(2 \, \left(\left(\left\|x\!\left(\left(k_{1} + 1\right)\right)\right\| \, \left\|x\!\left(k_{1}\right)\right\|\right) - \left|\operatorname{Re}\left(\left(x\!\left(\left(k_{1} + 1\right)\right) \, \operatorname{star}\!\left(x\!\left(k_{1}\right)\right)\right)\right)\right|\right)\right) \le \left(\left(K - 1\right) \, \left(\left(\left\|x\!\left(\left(k_{1} + 1\right)\right)\right\| - \left\|x\!\left(k_{1}\right)\right\|\right)\right)^{2}\right)\right)\bigr)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(\operatorname{kappa}\!\left(a\right) \le K\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.appellCoefficients`, `DerivativeChainPrefixLaws.kappa`, `DerivativeChainPrivate.IsChain`, `DerivativeChainPrivate.fromRoots` retain their exact imported definitions. Expand the exact squared chord identities and combine radial increments with the stated angular debit. Nondecreasing radii give the length and kappa estimates on that domain.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/ProjectiveRadialLift.lean, lines 87-98, SHA-256 6d6a602570440212aad59eb228068f2d9dfcd275d698f587dd48d93b41472a10. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_KappaDefinitions
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

theorem DerivativeChainPhaseLock.actual_paired_radial_kappa {n : ℕ} (a : Fin (n+1) → ℂ)
    (hc : ∀ j, Odd j → appellCoefficients (fromRoots a) j=0)
    (x : ℕ → ℂ) (hx : IsChain a (fun i => x i.val)) (hx0 : x 0=0)
    (hxend : x n ≠ 0) (K : ℝ) (hK : 0 ≤ K)
    (hr : ∀ k<n, ‖x k‖ ≤ ‖x (k+1)‖)
    (hang : ∀ k<n, 2*(‖x (k+1)‖*‖x k‖-|(x (k+1)*star (x k)).re|) ≤
      (K-1)*(‖x (k+1)‖-‖x k‖)^2) :
    DerivativeChainPrefixLaws.kappa a ≤ K := by sorry
