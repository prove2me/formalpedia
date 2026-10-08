-- Prove2me | Theorems.Thm_DaiWeissFluid_FBFS_inductive_step
-- name    : DaiWeissFluid.FBFS.inductive_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:38:37.143634+00:00
-- url     : https://prove2.me/theorems/f93f7ca0-9408-42fa-8214-de6370e5f00e
-- title:
--   Proof of Theorem 4.3 — the inductive step: once buffers 1, …, k−1 stay empty, buffer k empties by t_k
-- statement:
--   Consider a reentrant line with $m_k > 0$ and $\rho_i < 1$ for every station (1.7), and a solution $(Q,T)$ of the FBFS fluid model, i.e. (1.8)–(1.12) with (4.4) for $\pi(k) = k$. Fix a class $k$ and a time $\tau = t_{k-1} \ge 0$ such that all buffers $1,\dots,k-1$ are empty at every time $t \ge \tau$. Then buffer $k$ is empty at every time
--   $$
--   t \;\ge\; t_k \;=\; \tau + \frac{Q_k(\tau)\, m_k}{1 - \sum_{l\in H_k} m_l} .
--   $$
--
--   Here $H_k$ consists of the classes $l \le k$ served at station $\sigma(k)$, so $1 - \sum_{l\in H_k} m_l \ge 1 - \rho_{\sigma(k)} > 0$. Iterating over $k = 1,\dots,K$ is the induction that proves Theorem 4.3.
--
--   **Formalization Note** The paper's inductive hypothesis reads "stay empty for $t > t_{k-1}$"; the statement uses $t \ge t_{k-1}$, which is how the proof uses it (the two agree by continuity of $Q$). The paper writes "let the content … be $Q_k(t_{k-1}) > 0$"; the case $Q_k(t_{k-1}) = 0$ is also covered here, which is stronger. The paper's conclusion "buffer $k$ will be empty at time $t_k$ … and will stay empty at all times after $t_k$" is stated as $Q_k(t) = 0$ for all $t \ge t_k$. Classes are 0-based, so "buffers $1,\dots,k-1$" are the Lean indices $l < k$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 124, proof of Theorem 4.3 (inductive step)

import Mathlib
import Definitions.Def_DaiWeissFluid_FBFS_FluidModel

namespace DaiWeissFluid.FBFS

/-- The inductive step of the proof of Theorem 4.3, p. 124. In an FBFS fluid model, if at time
`τ = t_{k-1} ≥ 0` all classes before `k` are empty and stay empty from then on, then class `k` is
empty from time `t_k = τ + Q_k(τ) m_k / (1 - ∑_{l ∈ H_k} m_l)` on. -/
theorem inductive_step {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution (fbfs K) Q T)
    (k : Fin K) (τ : ℝ) (hτ : 0 ≤ τ) (hprev : ∀ t, τ ≤ t → ∀ l, l < k → Q t l = 0) :
    ∀ t, τ + Q τ k * L.m k / (1 - ∑ l ∈ L.H (fbfs K) k, L.m l) ≤ t → Q t k = 0 := by sorry

end DaiWeissFluid.FBFS
