-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_weighted_lipschitz_square_bound
-- name    : DerivativeChainPhaseLock.weighted_lipschitz_square_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:45:50.093928+00:00
-- url     : https://prove2.me/theorems/320e8891-ef19-4db6-baa6-629330f3f0fe
-- title:
--   Weighted lipschitz square bound
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $N\in \mathbb N$, $w\colon \bigl(I_{N}\longrightarrow \mathbb R\bigr)$, $a\colon \bigl(I_{N}\longrightarrow \mathbb C\bigr)$, $u\in \mathbb C$, $f\colon \bigl(I_{N}\longrightarrow \mathbb R\bigr)$, $T\in \mathbb R$. Assume
--
--   $$
--   \begin{aligned}
--   &\forall i\in I_{N},\quad \left(0 \le w\!\left(i\right)\right)\\
--   &\left(\sum_{i_{1}\in \mathsf{univ}} w\!\left(i_{1}\right) = 1\right)\\
--   &\left(\sum_{i_{2}\in \mathsf{univ}} \left(w\!\left(i_{2}\right) \, a\!\left(i_{2}\right)\right) = u\right)\\
--   &\forall i_{3}\in I_{N},\quad \left(0 \le f\!\left(i_{3}\right)\right)\\
--   &\forall i_{4}\in I_{N},\quad \forall j\in I_{N},\quad \left(\left|\left(f\!\left(i_{4}\right) - f\!\left(j\right)\right)\right| \le \left\|\left(a\!\left(i_{4}\right) - a\!\left(j\right)\right)\right\|\right)\\
--   &\left(0 \le T\right)\\
--   &\left(\sum_{i_{5}\in \mathsf{univ}} \left(w\!\left(i_{5}\right) \, f\!\left(i_{5}\right)\right) \le T\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(\sum_{i_{6}\in \mathsf{univ}} \left(w\!\left(i_{6}\right) \, \left(f\!\left(i_{6}\right)\right)^{2}\right) \le \left(\left(T\right)^{2} + \sum_{i_{7}\in \mathsf{univ}} \left(w\!\left(i_{7}\right) \, \left(\left\|\left(a\!\left(i_{7}\right) - u\right)\right\|\right)^{2}\right)\right)\right)
--   $$
--
--   Expand the weighted pairwise variance and use the stated Lipschitz bound to control the centered second moment.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/LipschitzSecondMoment.lean, lines 26-52, SHA-256 ecbeb327439275d399ee0eb7bd384374faf9ffb7d2216b1eb37f0bc6cc4ff7fb. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
open DerivativeChainContinuation
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.weighted_lipschitz_square_bound {N : ℕ} (w : Fin N → ℝ) (a : Fin N → ℂ)
    (u : ℂ) (f : Fin N → ℝ) (hw : ∀ i,0 ≤ w i) (hs : ∑ i,w i=1)
    (hm : ∑ i,(w i:ℂ)*a i=u) (hf : ∀ i,0 ≤ f i)
    (hlip : ∀ i j,|f i-f j| ≤ ‖a i-a j‖) (T : ℝ) (hT : 0 ≤ T)
    (hmean : (∑ i,w i*f i) ≤ T) :
    (∑ i,w i*(f i)^2) ≤ T^2+(∑ i,w i*‖a i-u‖^2) := by sorry
