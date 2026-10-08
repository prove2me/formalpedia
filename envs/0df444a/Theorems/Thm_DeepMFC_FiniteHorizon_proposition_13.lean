-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_proposition_13
-- name    : DeepMFC.FiniteHorizon.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:50.708512+00:00
-- url     : https://prove2.me/theorems/546ebdb9-8280-4065-9711-c7d84d037a71
-- title:
--   Proposition 13, p. 4076 — if two Lipschitz feedbacks differ by at most Γ on [0,T]×B̄_d(0,R), then |J^N(v) − J^N(w)| ≤ C(Γ² + 1/R)^{1/2}
-- statement:
--   Assume (A1)–(A4), (B1), (B3), (C1). For all $L,M\ge0$ there is a constant $C$ such that for every $N\ge1$ and all feedbacks $v,w$ that are $L$-Lipschitz in $(t,x)$ on $[0,T]\times\mathbb R^d$ with $|v(0,0)|,|w(0,0)|\le M$, and for all $\Gamma>0$ and $R>0$: if
--   $$\big\|v|_{[0,T]\times\bar B_d(0,R)}-w|_{[0,T]\times\bar B_d(0,R)}\big\|_{\mathcal C^0([0,T]\times\bar B_d(0,R))}\le\Gamma,\qquad(3.15)$$
--   then
--   $$|J^N(v)-J^N(w)|\le C\Big(\Gamma^2+\frac1R\Big)^{1/2},$$
--   where both costs are computed on the same Problem-3 space.
--
--   Closeness of two feedbacks on a large ball therefore controls the gap between their $N$-agent costs, uniformly in $N$; this is how the network approximation of Proposition 10 transfers to costs.
--
--   **Formalization Note.** The page says that $C$ depends on the data and the Lipschitz constants of $v,w$; its proof (p. 4092) also uses $v(0,0)$ and $w(0,0)$, and the bound cannot be uniform in them (constant feedbacks of growing size push the agents out of the ball). The statement here is that corrected reading: $C$ depends on $L$ and a bound $M$ for $|v(0,0)|,|w(0,0)|$. The sup-norm hypothesis (3.15) is stated pointwise on $[0,T]\times\bar B_d(0,R)$.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4076, Proposition 13, (3.15); dependence on v(0,0), w(0,0) from the proof, p. 4092

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem proposition_13 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D) :
    ∀ L Mφ : ℝ, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∀ v w : ℝ → E d → Fin k → ℝ, FeedbackLip M L v → ‖v 0 0‖ ≤ Mφ →
        FeedbackLip M L w → ‖w 0 0‖ ≤ Mφ →
      ∀ Γ R : ℝ, 0 < Γ → 0 < R →
        (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x ∈ Metric.closedBall (0 : E d) R, ‖v t x - w t x‖ ≤ Γ) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : Fin N → ℝ≥0 → Ω → E d)
        (X0 : Fin N → Ω → E d), Setting3 M P W X0 →
      ∀ Xv Xw : Fin N → ℝ≥0 → Ω → E d, Solves32 M P W X0 v Xv → Solves32 M P W X0 w Xw →
        |JN M P v Xv - JN M P w Xw| ≤ C * Real.sqrt (Γ ^ 2 + 1 / R) := by sorry

end DeepMFC.FiniteHorizon
