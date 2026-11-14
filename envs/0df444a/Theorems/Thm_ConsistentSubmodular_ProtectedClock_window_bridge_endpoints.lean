-- Prove2me | Theorems.Thm_ConsistentSubmodular_ProtectedClock_window_bridge_endpoints
-- name    : ConsistentSubmodular.ProtectedClock.window_bridge_endpoints
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:53.210197+00:00
-- url     : https://prove2.me/theorems/805ce477-c3aa-494b-978d-e2c7b733dc3c
-- title:
--   Both bridge endpoints of a clock window reach the next prefix scale
-- statement:
--   Let $C$ be a protected clock with window starts $s_0,s_1,\dots$, let $f$ be an objective on $[n]$ and $\kappa\in\mathbb N$, and let $i\in\mathbb N$. Let $X_t$ denote the arrived prefix after $t$ arrivals. For window $i$ put
--
--   * $\mathrm{buf}=X_{s_i+d_i}\setminus X_{s_i}$ with $d_i=s_{i+1}-s_i$ (the buffer of all arrivals during the window; the old set is $X_{s_i}$);
--   * $V=\mathrm{OPT}_\kappa(s_{i+1})=\max\{f(A):A\subseteq X_{s_{i+1}},|A|\le\kappa\}$ (the prefix optimum at the start of the next window);
--   * $T_i$, the best $\kappa$-subset of $X_{s_i}$ after adding $\mathrm{buf}$ (the terminal optimizer), and $I_{i+1}$, an optimal $\kappa$-subset of $X_{s_{i+1}}$ (the initial optimizer of window $i+1$).
--
--   Then
--
--   $$V\le f(\mathrm{buf}\cup T_i),\qquad V\le f(\mathrm{buf}\cup I_{i+1}),\qquad f(T_i)\le V,\qquad f(I_{i+1})\le V.$$
--
--   Both endpoints of the bridge between consecutive windows meet the next prefix scale $V$ under the protected old buffer, and neither exceeds it on its own. This provides the hypotheses of the rounded bridge between consecutive windows in the protected global schedule.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ClockWindows.lean#L72-L92 (`ConsistentSubmodular.ProtectedClock.window_bridge_endpoints`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)
variable {n : ℕ} (f : Objective n) (κ : ℕ)

theorem ConsistentSubmodular.ProtectedClock.window_bridge_endpoints (i : ℕ) :
    let buffer := C.windowBuffer n i (C.windowDuration i)
    let V := f.prefixOptimum κ (C.start (i + 1))
    V ≤ f.value (buffer ∪ C.windowTerminal f κ i) ∧
    V ≤ f.value (buffer ∪ C.windowInitial f κ (i + 1)) ∧
    f.value (C.windowTerminal f κ i) ≤ V ∧
    f.value (C.windowInitial f κ (i + 1)) ≤ V := by sorry
