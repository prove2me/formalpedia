-- Prove2me | Theorems.Thm_DaiWeissFluid_FBFS_emptying_time
-- name    : DaiWeissFluid.FBFS.emptying_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:39:03.121987+00:00
-- url     : https://prove2.me/theorems/71377330-07f1-4744-809f-27e79f8e4038
-- title:
--   Proof of Theorem 4.3 — every FBFS solution with |Q(0)| = 1 is empty from the explicit time δ on
-- statement:
--   Consider a reentrant line with $m_k > 0$ and $\rho_i < 1$ for every station (1.7), and a solution $(Q,T)$ of the FBFS fluid model with $|Q(0)| = \sum_k Q_k(0) = 1$. Then $Q_k(t) = 0$ for every class $k$ and every
--   $$
--   t \;\ge\; \delta = \sum_{k=1}^K \left( m_k\, \frac{\prod_{l=1}^{k-1}\bigl(1 - \sum_{j\in H_l\setminus\{l\}} m_j\bigr)}{\prod_{l=1}^{k}\bigl(1 - \sum_{j\in H_l} m_j\bigr)} \right),
--   $$
--   where $H_l$ is the set of classes $j \le l$ served at station $\sigma(l)$.
--
--   This explicit bound is the quantitative content of Theorem 4.3: it exhibits the time $\delta$ of Definition 1.3. For one class, $\delta = m_1/(1-m_1)$; for two classes at one station, $\delta = m_1/(1-m_1) + m_2/\bigl((1-m_1)(1-m_1-m_2)\bigr)$.
--
--   **Formalization Note** $\delta$ is the definition `fbfsEmptyingTime` of the definition module, in 0-based indices (products over $l < k$ and $l \le k$, $H_l\setminus\{l\}$ as `(H l).erase l`). The FBFS fluid model is `IsPrioritySolution (fbfs K)`.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 124, proof of Theorem 4.3 (the emptying time δ)

import Mathlib
import Definitions.Def_DaiWeissFluid_FBFS_FluidModel

namespace DaiWeissFluid.FBFS

/-- The emptying time of the proof of Theorem 4.3, p. 124: every solution of the FBFS fluid model
with `|Q(0)| = 1` is identically zero from time `δ = L.fbfsEmptyingTime` on. -/
theorem emptying_time {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution (fbfs K) Q T)
    (hQ0 : ∑ k, Q 0 k = 1) :
    ∀ t, L.fbfsEmptyingTime ≤ t → ∀ k, Q t k = 0 := by sorry

end DaiWeissFluid.FBFS
