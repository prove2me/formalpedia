-- Prove2me | Theorems.Thm_DischargeTiming_Ranking_proposition_2
-- name    : DischargeTiming.Ranking.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:54.905419+00:00
-- url     : https://prove2.me/theorems/1c73bb37-be45-4c11-8a90-089133960e4a
-- title:
--   Proposition 2, p. 15 — keeping a strongly dominant patient longer reduces the discharge cost by less
-- statement:
--   Consider the discharge cost $c_d(D)=\sum_{m,j}D^{m,j}R\,r(m,j)$ of form (8) with constant penalty $R_t=R$, under the standing assumptions ($r(m,\cdot)$ continuously differentiable and nonincreasing on $[0,\infty)$, $R\ge0$). Let $(m_1,t_1)\succ(m_2,t_2)$ in the sense of strong dominance (15), let $D_k$ and $D_{k'}$ be any two discharge actions, and let $k<k'$ be epochs such that $t_1+k'-k\le J$ and $t_2+k'-k\le J$. Then
--   $$c_d\bigl(D_k+e_{(m_1,t_1)}\bigr)-c_d\bigl(D_{k'}+e_{(m_1,t_1+k'-k)}\bigr)\;\le\;c_d\bigl(D_k+e_{(m_2,t_2)}\bigr)-c_d\bigl(D_{k'}+e_{(m_2,t_2+k'-k)}\bigr).$$
--
--   In words: postponing the discharge of a $(m_1,t_1)$ patient by $k'-k$ days lowers the expected readmission penalty by no more than postponing that of a $(m_2,t_2)$ patient by the same number of days. It is the cost comparison behind the interchange argument of Theorem 2.
--
--   **Formalization Note** The positions $t_i+k'-k$ must be LOS indices in $\{0,\dots,J\}$ for $e_{(m_i,t_i+k'-k)}$ to exist; this is stated as the hypotheses $t_1+k'-k\le J$, $t_2+k'-k\le J$. The LOS values $t_1,t_2$ are cast to real numbers in (15).
-- source:
--   Shi, Helm, Deglise-Hawkinson, Pan, Timing it right: balancing inpatient congestion versus readmission risk at discharge, SSRN working paper 3202975 (version of 2019-08-26), p. 15, Proposition 2 (proof: Appendix B.2, p. 45)

import Mathlib
import Definitions.Def_DischargeTiming_Ranking_Model

namespace DischargeTiming.Ranking

theorem proposition_2 {M J : ℕ} (P : Model M J) (hP : P.Standing)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1))
    (hdom : StronglyDominates P m1 ((t1 : ℕ) : ℝ) m2 ((t2 : ℕ) : ℝ))
    (Dk Dk' : Action M J) (k k' : ℕ) (hkk' : k < k')
    (h1 : (t1 : ℕ) + (k' - k) ≤ J) (h2 : (t2 : ℕ) + (k' - k) ≤ J) :
    dischargeCost P (Dk + unitAction m1 t1)
        - dischargeCost P (Dk' + unitAction m1 (losShift t1 (k' - k) h1))
      ≤ dischargeCost P (Dk + unitAction m2 t2)
        - dischargeCost P (Dk' + unitAction m2 (losShift t2 (k' - k) h2)) := by sorry

end DischargeTiming.Ranking
