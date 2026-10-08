-- Prove2me | Theorems.Thm_DaiWeissFluid_LBFS_drift_bound
-- name    : DaiWeissFluid.LBFS.drift_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:43:21.904734+00:00
-- url     : https://prove2.me/theorems/dfd449ed-b085-4808-9022-d62f7443665a
-- title:
--   Proof of Theorem 4.4 — negative drift of total fluid content
-- statement:
--   Let a reentrant line have at least one class, positive mean service times $m_k$, and station workloads $\rho_i<1$. Consider any solution of the Last-Buffer-First-Served (LBFS) priority fluid model. At a regular time $t>0$ when total fluid content $G(t)=|Q(t)|=\sum_k Q_k(t)$ is positive, write $\dot G(t)$ for its derivative and set $\hat\lambda=1/\max_i\rho_i$. Then
--   $$
--   \dot G(t)\le 1-\hat\lambda<0.
--   $$
--   The constant is uniform across all solutions and regular times. It is the quantitative estimate used to obtain the emptying time in Theorem 4.4.
--
--   **Formalization Note** Classes and stations use 0-based `Fin` indices, and LBFS is `Fin.revPerm`. A regular point is encoded by derivatives of every service path $T_k$ and of $G$. The explicit assumption $K>0$ excludes the empty route, for which $\max_i\rho_i$ need not be positive and its reciprocal would use division by zero in Lean. The paper's route has at least one stage. The paper prints the bound with a strict inequality, $\dot G(t) < 1-\hat\lambda$; it has just derived $\lambda \ge \hat\lambda$, and equality is attained (one station, one class, $m_1 = 1/2$, $Q_1(t) = 1-t$ on $[0,1)$: $\dot G = -1 = 1-\hat\lambda$), so the strict reading is false and the bound is stated with $\le$.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 124–125, proof of Theorem 4.4 (drift inequality)

import Mathlib
import Definitions.Def_DaiWeissFluid_LBFS_FluidModel

namespace DaiWeissFluid.LBFS

/-- The negative drift established in the proof of Theorem 4.4, pp. 124–125. The page prints
`Ġ(t) < 1 − λ̂`; it has just derived `λ ≥ λ̂`, and equality holds in a one-class line, so the bound
is stated with `≤`. -/
theorem drift_bound {I K : ℕ} (L : ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hρ : ∀ i, L.ρ i < 1) (hK : 0 < K)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution Fin.revPerm Q T)
    (t : ℝ) (ht : 0 < t) (dT : Fin K → ℝ)
    (hdT : ∀ k, HasDerivAt (fun s => T s k) (dT k) t)
    (hpos : 0 < ∑ k, Q t k) (g : ℝ)
    (hg : HasDerivAt (fun s => ∑ k, Q s k) g t) :
    g ≤ 1 - L.lamHat ∧ 1 < L.lamHat := by sorry

end DaiWeissFluid.LBFS
