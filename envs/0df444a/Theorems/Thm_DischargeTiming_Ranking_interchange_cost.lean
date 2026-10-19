-- Prove2me | Theorems.Thm_DischargeTiming_Ranking_interchange_cost
-- name    : DischargeTiming.Ranking.interchange_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:54.708298+00:00
-- url     : https://prove2.me/theorems/66da8555-254f-4f42-94c3-71003f8b2fa2
-- title:
--   Proof of Theorem 2, p. 16 — the interchanged schedule is feasible and costs no more: V^π2 − V^π1 ≤ 0
-- statement:
--   Work under the standing assumptions ($r(m,\cdot)$ continuously differentiable and nonincreasing on $[0,\infty)$, $R\ge0$). Fix an initial state, an exogenous arrival path, a horizon $H$ and a feasible schedule $D$ (the policy $\pi_1$) with trajectory $(X_i)$. Let $(m_1,t_1)\succ(m_2,t_2)$ be strongly dominating types with $\underline L_{m_1}\le t_1$, let $k<k'\le H$, $\Delta=k'-k$, with $t_1+\Delta\le J$ and $t_2+\Delta\le J$. Assume $D_k^{m_2,t_2}\ge1$, $D_k^{m_1,t_1}<X_k^{m_1,t_1}$, and that the kept $(m_1,t_1)$ cohort is discharged at $k'$ ($D_{k'}^{m_1,t_1+\Delta}\ge1$ if $k'<H$) or is present at the horizon ($X_H^{m_1,t_1+\Delta}\ge1$ if $k'=H$).
--
--   Let $D'$ (the policy $\pi_2$) be the interchanged schedule, which discharges the $(m_1,t_1)$ patient at $k$ and the $(m_2,t_2)$ patient at $k'$ instead. Then $D'$ is feasible on the horizon $H$ and
--   $$V^{\pi_2}-V^{\pi_1}=c_d(D_k+e_{(m_1,t_1)})+c_d(D_{k'}+e_{(m_2,t_2+k'-k)})-c_d(D_k+e_{(m_2,t_2)})-c_d(D_{k'}+e_{(m_1,t_1+k'-k)})\le 0,$$
--   that is, the total cost of $D'$ is at most that of $D$.
--
--   This is the single interchange step of the proof of Theorem 2, in the case treated in the main text, where both interchanged patients stay within the maximum LOS.
--
--   **Formalization Note** Total cost is the finite-horizon cost with terminal valuation of the mission's model. The hypothesis $\underline L_{m_1}\le t_1$ is added: the extra $(m_1,t_1)$ discharge at $k$ must respect the minimum LOS (4). The page's case condition "$t_1+k'-k\le J$, i.e. that $k'$ is not beyond type $(m_2,t_2)$ patient's maximum LOS" is stated for both patients, $t_1+\Delta\le J$ and $t_2+\Delta\le J$, which is what makes both shifted unit vectors exist.
-- source:
--   Shi, Helm, Deglise-Hawkinson, Pan, Timing it right: balancing inpatient congestion versus readmission risk at discharge, SSRN working paper 3202975 (version of 2019-08-26), pp. 15–16, proof of Theorem 2 (display V^π2 − V^π1 ≤ 0, p. 16)

import Mathlib
import Definitions.Def_DischargeTiming_Ranking_Model

namespace DischargeTiming.Ranking

theorem interchange_cost {M J : ℕ} (P : Model M J) (hP : P.Standing) (x0 : State M J)
    (arr : ℕ → Fin M → ℕ) (H : ℕ) (D : ℕ → Action M J)
    (hD : FeasibleSchedule P x0 arr H D)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1))
    (hdom : StronglyDominates P m1 ((t1 : ℕ) : ℝ) m2 ((t2 : ℕ) : ℝ))
    (hL : P.L m1 ≤ t1)
    (k k' : ℕ) (hkk' : k < k') (hk'H : k' ≤ H)
    (h1 : (t1 : ℕ) + (k' - k) ≤ J) (h2 : (t2 : ℕ) + (k' - k) ≤ J)
    (hD2 : 1 ≤ D k m2 t2) (hD1 : D k m1 t1 < traj x0 arr D k m1 t1)
    (hlate : k' < H → 1 ≤ D k' m1 (losShift t1 (k' - k) h1))
    (hterm : k' = H → 1 ≤ traj x0 arr D H m1 (losShift t1 (k' - k) h1)) :
    FeasibleSchedule P x0 arr H
        (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2 (losShift t2 (k' - k) h2))
      ∧ totalCost P x0 arr H
          (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2 (losShift t2 (k' - k) h2))
          - totalCost P x0 arr H D
        = dischargeCost P (unitAction m1 t1)
            + dischargeCost P (unitAction m2 (losShift t2 (k' - k) h2))
            - dischargeCost P (unitAction m2 t2)
            - dischargeCost P (unitAction m1 (losShift t1 (k' - k) h1))
      ∧ totalCost P x0 arr H
          (interchange D k k' m1 t1 (losShift t1 (k' - k) h1) m2 t2 (losShift t2 (k' - k) h2))
        ≤ totalCost P x0 arr H D := by sorry

end DischargeTiming.Ranking
