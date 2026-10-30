-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_large_gain_rms_budget
-- name    : DerivativeChainPhaseLock.large_gain_rms_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:47:17.846683+00:00
-- url     : https://prove2.me/theorems/15834b80-4389-41a9-83d4-a8ea2fa39811
-- title:
--   Large gain rms budget
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $K\in \mathbb R$, $A2\in \mathbb R$, $v\in \mathbb R$, $D\in \mathbb R$, $B2\in \mathbb R$. Assume
--
--   $$
--   \begin{aligned}
--   &\left(0 < K\right)\\
--   &\left(0 \le v\right)\\
--   &\left(v \le D\right)\\
--   &\left(0 \le B2\right)\\
--   &\left(A2 \le \left(K \, v\right)\right)\\
--   &\left(\sqrt{B2} \le \left(\sqrt{A2} + \sqrt{\left(D - v\right)}\right)\right)\\
--   &\left(\left(D = 0\right) \lor \left(\sqrt{\frac{v}{D}} \le \frac{\left(K - 1\right)}{\left(K + 1\right)}\right)\right)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(B2 \le \left(K \, D\right)\right)
--   $$
--
--   Insert the retained-prefix variance gain into the root-mean-square extension estimate and simplify the resulting budget inequality.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/LargeGainBudget.lean, lines 5-26, SHA-256 aec7fd3d09d94c8b7615e4d36dd4023d1b61b2b94c8b0892398811ed12fe05aa. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.large_gain_rms_budget (K A2 v D B2 : ℝ) (hK : 0 < K) (hv : 0 ≤ v)
    (hvd : v ≤ D) (hB : 0 ≤ B2) (hchild : A2 ≤ K*v)
    (hrms : Real.sqrt B2 ≤ Real.sqrt A2+Real.sqrt (D-v))
    (hgain : D=0 ∨ Real.sqrt (v/D) ≤ (K-1)/(K+1)) : B2 ≤ K*D := by sorry
