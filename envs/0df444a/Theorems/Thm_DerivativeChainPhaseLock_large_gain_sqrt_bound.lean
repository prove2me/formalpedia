-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_large_gain_sqrt_bound
-- name    : DerivativeChainPhaseLock.large_gain_sqrt_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:45:57.782967+00:00
-- url     : https://prove2.me/theorems/7d291989-ce89-417b-8c3c-afdb51433d33
-- title:
--   Large gain sqrt bound
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $K\in \mathbb R$, $v\in \mathbb R$, $D\in \mathbb R$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(0 \le K\right)\\
--   &\left(0 \le v\right)\\
--   &\left(v \le D\right)\\
--   &\left(\left(\left(K + 1\right) \, \sqrt{v}\right) \le \left(\left(K - 1\right) \, \sqrt{D}\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(\left(\sqrt{\left(K \, v\right)} + \sqrt{\left(D - v\right)}\right) \le \sqrt{\left(K \, D\right)}\right)
--   $$
--
--   Square the displayed nonnegative quantities and simplify the resulting scalar inequalities on the stated variance-gain domain.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/LargeGainScalar.lean, lines 6-24, SHA-256 8cb9adbf9f8d19de22dfb488c26fee706121255df04eb33e8f50f254cb62fc56. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
set_option maxHeartbeats 1000000
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.large_gain_sqrt_bound (K v D : ℝ) (hK : 0 ≤ K) (hv : 0 ≤ v)
    (hvd : v ≤ D)
    (hgain : (K+1)*Real.sqrt v ≤ (K-1)*Real.sqrt D) :
    Real.sqrt (K*v)+Real.sqrt (D-v) ≤ Real.sqrt (K*D) := by sorry
