-- Prove2me | Theorems.Thm_ConsistentSubmodular_ProtectedClock_retained_tests_prefix
-- name    : ConsistentSubmodular.ProtectedClock.retained_tests_prefix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:38.554733+00:00
-- url     : https://prove2.me/theorems/aa19bad5-595b-4b3a-b117-00a67fedd18c
-- title:
--   Retained physical tests extend to all real updates at a uniform relative loss
-- statement:
--   Let $C$ be a protected clock with window starts $s_i$, let $f$ be an objective on $[n]$, $\kappa\in\mathbb N$, let $O$ be a certificate family with level $\alpha=O.\mathrm{level}$, let $N>0$ and $i\in\mathbb N$. Let $W$ be the fractional window of index $i$ (old set $X_{s_i}$, buffers $Q_u=X_{s_i+u}\setminus X_{s_i}$, duration $s_{i+1}-s_i$) with retained times $r_0,\dots,r_{3N+1}$, where $X_t$ is the arrived prefix after $t$ arrivals. Write $\mathrm{OPT}_\kappa(t)=\max\{f(A'):A'\subseteq X_t,|A'|\le\kappa\}$ and $\mathrm{OPT}(\mathrm{old},Q)=\max\{f(Q\cup C'):C'\subseteq X_{s_i},|C'|\le\kappa\}$. Let $A\subseteq[n]$ satisfy, for every retained index $j$,
--
--   $$\alpha\,\mathrm{OPT}(X_{s_i},Q_{r_j})-\frac{\mathrm{OPT}_\kappa(s_i)}{N}\;\le\;f\big(Q_{r_j}\cup A\big).$$
--
--   Then for every $t$ with $s_i\le t\le s_{i+1}$,
--
--   $$\Big(\alpha-\frac2N\Big)\,\mathrm{OPT}_\kappa(t)\;\le\;f\big(A\cup(X_t\setminus X_{s_i})\big).$$
--
--   Retained physical tests therefore extend to all real updates of the window at a uniform relative loss $2/N$. This is the checkpoint property needed by the protected global schedule.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ClockWindows.lean#L116-L150 (`ConsistentSubmodular.ProtectedClock.retained_tests_prefix`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)
variable {n : ℕ} (f : Objective n) (κ : ℕ)

theorem ConsistentSubmodular.ProtectedClock.retained_tests_prefix (O : CertificateFamily) (N : ℕ) (hN : 0 < N) (i : ℕ)
    (A : Finset (Fin n))
    (htests : ∀ j, let W := C.fractionalWindows f κ O N hN i
      O.level * f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i (W.retained j)) κ-
        f.prefixOptimum κ (C.start i) / N ≤ f.value (C.windowBuffer n i (W.retained j) ∪ A)) :
    ∀ t, C.start i ≤ t → t ≤ C.start (i + 1) →
      (O.level - 2 / N) * f.prefixOptimum κ t ≤
        f.value (A ∪ (arrivedPrefix n t\arrivedPrefix n (C.start i))) := by sorry
