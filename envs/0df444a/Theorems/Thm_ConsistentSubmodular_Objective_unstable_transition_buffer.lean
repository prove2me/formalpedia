-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_unstable_transition_buffer
-- name    : ConsistentSubmodular.Objective.unstable_transition_buffer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:31.716412+00:00
-- url     : https://prove2.me/theorems/bb13cad9-0cf9-4d71-ac29-4b56af53500e
-- title:
--   Rolling buffer is a $\tfrac34$-approximation during an unstable transition
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on a stream of length $n$, let $k\in\mathbb N$, and let $F(t)=\max\{f(A):A\subseteq X_t,\ |A|\le k\}$ be the prefix optimum after $t$ arrivals. Let $\eta\in\mathbb R$ and $b,\ell\in\mathbb N$, and let $C$ be a protected clock for $F$ with parameters $(\eta,b,\ell)$, with start times $\sigma_i=C.\mathrm{start}(i)$ satisfying $(i+1)b\le\sigma_i$, $\sigma_i+\ell\le(i+2)b$ and the protection property. Let $i,t\in\mathbb N$ with
--   $$\sigma_i\le t\le\sigma_i+\ell\qquad\text{and}\qquad 4\,F\bigl((i+1)b\bigr)\le F(\sigma_i).$$
--   Then the rolling buffer $X_t\setminus X_{t-4b}$ of the last $4b$ arrivals satisfies
--   $$\tfrac34\,F(t)\;\le\;f\bigl(X_t\setminus X_{t-4b}\bigr).$$
--
--   In the reduction to window instances, a block either contains a stable interval or the optimum has grown fourfold since the block start. In the latter, unstable case, the buffer of the most recent $4b$ elements already is a $\tfrac34$-approximation of the optimum throughout the transition interval.
--
--   **Formalization Note**: the buffer is `rollingBuffer n (4*b) t`, with truncated natural subtraction $t-4b$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ProtectedClock.lean#L131-L146 (`ConsistentSubmodular.Objective.unstable_transition_buffer`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProtectedClock

open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.unstable_transition_buffer (k : ℕ) {η : ℝ} {b ell : ℕ}
    (C : ProtectedClock (f.prefixOptimum k) η b ell) (i t : ℕ)
    (ht0 : C.start i ≤ t) (ht1 : t ≤ C.start i + ell)
    (hu : 4 * f.prefixOptimum k ((i + 1) * b) ≤ f.prefixOptimum k (C.start i)) :
    (3 : ℝ) / 4 * f.prefixOptimum k t ≤ f.value (rollingBuffer n (4 * b) t) := by sorry
