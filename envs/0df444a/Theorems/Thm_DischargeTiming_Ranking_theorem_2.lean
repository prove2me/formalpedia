-- Prove2me | Theorems.Thm_DischargeTiming_Ranking_theorem_2
-- name    : DischargeTiming.Ranking.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:59.226824+00:00
-- url     : https://prove2.me/theorems/f7e1a485-0af8-4345-ace8-a0b6eda7f9d1
-- title:
--   Theorem 2, p. 15 (corrected: t2 ≤ t1) — a no-costlier feasible schedule discharges (m2,t2) only after all (m1,t1) when (m1,t1) ≻ (m2,t2)
-- statement:
--   Consider the discharge model with discharge cost $c_d$ of form (8) and constant penalty $R_t=R$, under the standing assumptions ($r(m,\cdot)$ continuously differentiable and nonincreasing on $[0,\infty)$, $R\ge0$). Fix an initial state $X_0$, an exogenous arrival path (new arrivals and readmissions), and a horizon $H$. Let $(m_1,t_1)$ and $(m_2,t_2)$ be two **distinct** patient types with
--   1. $(m_1,t_1)\succ(m_2,t_2)$ (strong dominance (15));
--   2. $t_2\le t_1$;
--   3. $\underline L_{m_1}\le t_1$, so that $(m_1,t_1)$ patients may be discharged.
--
--   Then for every feasible discharge schedule $D$ there is a feasible schedule $D'$ with $V(D')\le V(D)$ such that, at every epoch $k<H$,
--   $$D'_k\cdot e_{(m_2,t_2)}>0\ \Longrightarrow\ D'_k\cdot e_{(m_1,t_1)}=X'_k\cdot e_{(m_1,t_1)},$$
--   where $(X'_k)$ is the trajectory of $D'$: a $(m_2,t_2)$ patient is discharged only if all $(m_1,t_1)$ patients are discharged. In particular, since the feasible schedules are finitely many, some optimal schedule follows this rule.
--
--   The result ranks patients for discharge by marginal rather than absolute readmission risk: among two types, the one whose risk falls more slowly with further stay is discharged first.
--
--   **Formalization Note** This corrects Theorem 2 as printed, which is false without $t_2\le t_1$: with $J=3$, $N=1$, $C=1000$, $R=1$, no arrivals, $r(1,j)=10-j$, $r(2,j)=10-2j$ and one $(1,0)$ and one $(2,2)$ patient at epoch $0$, we have $(1,0)\succ(2,2)$, yet (on a horizon $H\ge3$) the unique optimum discharges the $(2,2)$ patient alone (cost 1013), while every schedule obeying the rule costs at least 1014. The failing case is the one of Appendix B.3, where the dominated patient would pass the maximum LOS; it cannot arise when $t_2\le t_1$. The hypotheses "distinct types" (strong dominance is reflexive) and $\underline L_{m_1}\le t_1$ are added because the rule is false without them. "The optimal discharge action" over the long-run average cost (9) is replaced by the pathwise finite-horizon statement in which the paper's interchange argument lives (arrivals exogenous, Remark 4), and the conclusion is "some no-costlier schedule obeys the rule", because with ties (equal slopes) an optimal schedule may break it.
-- source:
--   Shi, Helm, Deglise-Hawkinson, Pan, Timing it right: balancing inpatient congestion versus readmission risk at discharge, SSRN working paper 3202975 (version of 2019-08-26), p. 15, Theorem 2 (corrected; see Formalization Note); proof pp. 15–16 and Appendix B.3, pp. 45–46

import Mathlib
import Definitions.Def_DischargeTiming_Ranking_Model

namespace DischargeTiming.Ranking

theorem theorem_2 {M J : ℕ} (P : Model M J) (hP : P.Standing) (x0 : State M J)
    (arr : ℕ → Fin M → ℕ) (H : ℕ) (D : ℕ → Action M J)
    (hD : FeasibleSchedule P x0 arr H D)
    (m1 m2 : Fin M) (t1 t2 : Fin (J + 1))
    (hdom : StronglyDominates P m1 ((t1 : ℕ) : ℝ) m2 ((t2 : ℕ) : ℝ))
    (hne : (m1, t1) ≠ (m2, t2)) (hle : t2 ≤ t1) (hL : P.L m1 ≤ t1) :
    ∃ D' : ℕ → Action M J, FeasibleSchedule P x0 arr H D' ∧
      totalCost P x0 arr H D' ≤ totalCost P x0 arr H D ∧
      ∀ k < H, 0 < D' k m2 t2 → D' k m1 t1 = traj x0 arr D' k m1 t1 := by sorry

end DischargeTiming.Ranking
