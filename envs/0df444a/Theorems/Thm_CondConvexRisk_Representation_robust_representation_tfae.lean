-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_robust_representation_tfae
-- name    : CondConvexRisk.Representation.robust_representation_tfae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:59:19.152075+00:00
-- url     : https://prove2.me/theorems/f62265a5-2d90-4dcf-8410-56ef3da0c8fc
-- title:
--   Theorem 3.2 — robust representation of conditional convex risk measures
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\mathcal G\subseteq\mathcal F$ a sub-$\sigma$-algebra, and $\rho:L^\infty\to L^\infty_{\mathcal G}$ a conditional convex risk measure. The following are equivalent:
--   1. $\rho$ is continuous from above: $X_n\searrow X$ $P$-a.s. implies $\rho(X_n)\nearrow\rho(X)$ $P$-a.s.;
--   2. $\rho$ is representable: there is a penalty $\alpha:\mathcal P_{\mathcal G}\to L^0_{\mathcal G}([0,+\infty])$ with
--   $$\rho(X)=\operatorname*{ess.sup}_{Q\in\mathcal P_{\mathcal G}}\{-E_Q(X\mid\mathcal G)-\alpha(Q)\},\qquad X\in L^\infty;$$
--   3. $\rho$ is representable in terms of the minimal penalty
--   $$\alpha^*(Q)=\operatorname*{ess.sup}_{X\in L^\infty}\{-E_Q(X\mid\mathcal G)-\rho(X)\},\qquad Q\in\mathcal P_{\mathcal G}.$$
--
--   This is the conditional analogue of the robust representation of convex risk measures: the expectations become conditional, the penalty becomes random, the supremum is essential, and only models agreeing with $P$ on the available information enter.
--
--   **Formalization Note** Statement 3 is: some $\alpha^*$ that is the essential supremum of $B_Q$ for every $Q$ (taken $\mathcal G$-measurable and $[0,+\infty]$-valued, which an essential supremum of $B_Q$ can always be chosen to be) is a penalty function for $\rho$. All (in)equalities are $P$-a.s.; the essential supremum is the predicate of the appendix definitions.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 6, Theorem 3.2

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem robust_representation_tfae {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ) :
    List.TFAE
      [IsContinuousFromAbove P ρ,
       IsRepresentable m P ρ,
       ∃ α : PG m P → Ω → ENNReal,
         IsMinimalPenalty m P ρ α ∧ IsPenaltyFor m P ρ α] := by sorry

end CondConvexRisk.Representation
