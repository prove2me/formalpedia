-- Prove2me | Theorems.Thm_DaiWeissFluid_LBFS_emptying_time
-- name    : DaiWeissFluid.LBFS.emptying_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:43:45.800144+00:00
-- url     : https://prove2.me/theorems/6702d2ab-2108-4557-9fcf-f740a13ba793
-- title:
--   Proof of Theorem 4.4 — explicit LBFS emptying time
-- statement:
--   Let a reentrant line have at least one class, positive mean service times $m_k$, and station workloads $\rho_i<1$. For every LBFS priority fluid solution, put $|Q(0)|=\sum_kQ_k(0)$ and $\hat\lambda=1/\max_i\rho_i$. Every buffer is empty and remains empty by the time
--   $$
--   \delta=\frac{|Q(0)|}{\hat\lambda-1}.
--   $$
--   Thus $Q_k(t)=0$ for every class $k$ and every $t\ge\delta$. This bound holds for every initial fluid level, before normalizing $|Q(0)|=1$ in Definition 1.3.
--
--   **Formalization Note** Classes are 0-based. The assumption $K>0$ makes the maximum station workload positive under $m_k>0$, so $\hat\lambda>1$ and the denominator is positive. For $|Q(0)|=0$, the statement includes $t=0$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 125, proof of Theorem 4.4 (emptying time)

import Mathlib
import Definitions.Def_DaiWeissFluid_LBFS_FluidModel

namespace DaiWeissFluid.LBFS

/-- The explicit uniform extinction time in the proof of Theorem 4.4, p. 125. -/
theorem emptying_time {I K : ℕ} (L : ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hρ : ∀ i, L.ρ i < 1) (hK : 0 < K)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution Fin.revPerm Q T) :
    ∀ t, (∑ k, Q 0 k) / (L.lamHat - 1) ≤ t → ∀ k, Q t k = 0 := by sorry

end DaiWeissFluid.LBFS
