-- Prove2me | Theorems.Thm_DaiWeissFluid_FBFS_theorem4_3
-- name    : DaiWeissFluid.FBFS.theorem4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:39:31.956377+00:00
-- url     : https://prove2.me/theorems/46dc0636-b465-4672-956b-7888346f218a
-- title:
--   Theorem 4.3 — the FBFS fluid model of every reentrant line is stable
-- statement:
--   Consider any reentrant line with $I$ stations and $K$ classes, mean service times $m_k > 0$, and nominal workloads satisfying
--   $$
--   \rho_i = \sum_{k\in C_i} m_k < 1 \qquad (i = 1,\dots,I). \tag{1.7}
--   $$
--   Then the fluid model corresponding to the First-Buffer-First-Served discipline, i.e. (1.8)–(1.12) together with the preemptive-resume priority condition (4.4) for $\pi(k) = k$, is stable: there is a time $\delta > 0$ such that every solution with $|Q(0)| = 1$ satisfies $Q_k(t) = 0$ for all $t \ge \delta$ and all classes $k$.
--
--   By the paper's Theorem 1.1 (Dai 1995), stability of this fluid model implies positive Harris recurrence of the corresponding multiclass queueing network under FBFS whenever (1.7) holds, the stochastic analogue of Kumar's result for deterministic systems.
--
--   **Formalization Note** The statement quantifies over every line: all $I$, $K$, routes $\sigma$ and service times $m$. The positivity $m_k > 0$ is explicit (the paper takes it for granted, since $\mu_k = 1/m_k$). Condition (1.13) is not added, since (4.4) supersedes it (p. 123). Stability is Definition 1.3, `FluidStable`. Classes and stations are 0-based.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 124, Theorem 4.3

import Mathlib
import Definitions.Def_DaiWeissFluid_FBFS_FluidModel

namespace DaiWeissFluid.FBFS

/-- Theorem 4.3, p. 124: in every reentrant line satisfying (1.7), the fluid model of the
First-Buffer-First-Served discipline, (1.8)–(1.12) with (4.4) for `π(k) = k`, is stable
(Definition 1.3). -/
theorem theorem4_3 {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) :
    DaiWeissFluid.ThreeBuffer.FluidStable (L.IsPrioritySolution (fbfs K)) := by sorry

end DaiWeissFluid.FBFS
