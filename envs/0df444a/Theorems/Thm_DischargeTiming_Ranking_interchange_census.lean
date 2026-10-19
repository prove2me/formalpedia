-- Prove2me | Theorems.Thm_DischargeTiming_Ranking_interchange_census
-- name    : DischargeTiming.Ranking.interchange_census
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:54.438919+00:00
-- url     : https://prove2.me/theorems/58cceda8-413b-48d0-b627-2fcef2a60cb5
-- title:
--   Proof of Theorem 2, p. 16 — the interchange leaves the census unchanged at every epoch
-- statement:
--   Fix an initial state $X_0$, an exogenous arrival path, a horizon $H$ and a feasible discharge schedule $D$ with trajectory $(X_i)$. Let $k<k'\le H$, put $\Delta=k'-k$, and let $(m_1,t_1)$, $(m_2,t_2)$ be types with $t_1+\Delta\le J$ and $t_2+\Delta\le J$. Suppose that at epoch $k$ at least one $(m_2,t_2)$ patient is discharged, $D_k^{m_2,t_2}\ge1$, while some $(m_1,t_1)$ patient is kept, $D_k^{m_1,t_1}<X_k^{m_1,t_1}$; and that the same $m_1$-cohort is still present at $k'$: if $k'<H$ then $D_{k'}^{m_1,t_1+\Delta}\ge1$, and if $k'=H$ then $X_H^{m_1,t_1+\Delta}\ge1$.
--
--   Let $D'$ be the interchanged schedule: $D'_k=D_k+e_{(m_1,t_1)}-e_{(m_2,t_2)}$, $D'_{k'}=D_{k'}-e_{(m_1,t_1+\Delta)}+e_{(m_2,t_2+\Delta)}$, and $D'_i=D_i$ otherwise. Then the census of the two trajectories agrees at every epoch:
--   $$S\bigl(X'_i\bigr)=S\bigl(X_i\bigr)\qquad\text{for all } i\le H.$$
--
--   This is the first step of the interchange argument: "the occupancies are the same under both policies under all sample paths", so the holding costs of the two schedules coincide.
--
--   **Formalization Note** When $k'=H$ the action at $k'$ is never used, and the kept $(m_1,t_1)$ patient is the one present at the horizon. The hypothesis $D_{k'}^{m_1,t_1+\Delta}\ge1$ (or $X_H^{m_1,t_1+\Delta}\ge1$) identifies a later discharge (or the presence at the horizon) of a member of the cohort of the kept patient, which is how the page's "is discharged at a later time, $k'$" is read.
-- source:
--   Shi, Helm, Deglise-Hawkinson, Pan, Timing it right: balancing inpatient congestion versus readmission risk at discharge, SSRN working paper 3202975 (version of 2019-08-26), pp. 15–16, proof of Theorem 2 ('The first equality follows because the occupancies are the same under both policies under all sample paths', p. 16)

import Mathlib
import Definitions.Def_DischargeTiming_Ranking_Model

namespace DischargeTiming.Ranking

theorem interchange_census {M J : ℕ} (P : Model M J) (x0 : State M J)
    (arr : ℕ → Fin M → ℕ) (H : ℕ) (D : ℕ → Action M J)
    (hD : FeasibleSchedule P x0 arr H D)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1)) (k k' : ℕ) (hkk' : k < k') (hk'H : k' ≤ H)
    (h1 : (t1 : ℕ) + (k' - k) ≤ J) (h2 : (t2 : ℕ) + (k' - k) ≤ J)
    (hD2 : 1 ≤ D k m2 t2) (hD1 : D k m1 t1 < traj x0 arr D k m1 t1)
    (hlate : k' < H → 1 ≤ D k' m1 (losShift t1 (k' - k) h1))
    (hterm : k' = H → 1 ≤ traj x0 arr D H m1 (losShift t1 (k' - k) h1)) :
    ∀ i ≤ H,
      census (traj x0 arr
          (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2 (losShift t2 (k' - k) h2)) i)
        = census (traj x0 arr D i) := by sorry

end DischargeTiming.Ranking
