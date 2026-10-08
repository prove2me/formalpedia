-- Prove2me | Theorems.Thm_ConvexRiskFn_Cont_proposition_3_1
-- name    : ConvexRiskFn.Cont.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:52.887678+00:00
-- url     : https://prove2.me/theorems/0ae7608a-b43a-44ce-ac1c-cdfdd1c5ed20
-- title:
--   Proposition 3.1, p. 437 — on a Banach lattice, a proper ρ satisfying (A1)–(A2) is continuous and subdifferentiable on int(dom ρ)
-- statement:
--   Let $\mathcal X$ be a **Banach lattice**: a real Banach space with a lattice order compatible with addition such that $|X_1|\le|X_2|$ implies $\|X_1\|\le\|X_2\|$. Let $\rho:\mathcal X\to\overline{\mathbb R}$ be **proper** ($\rho>-\infty$ everywhere and $\operatorname{dom}\rho=\{\rho<+\infty\}\ne\emptyset$) and satisfy
--
--   1. (A1) convexity: $\rho(\alpha X+(1-\alpha)Y)\le\alpha\rho(X)+(1-\alpha)\rho(Y)$ for $X,Y\in\mathcal X$, $\alpha\in[0,1]$;
--   2. (A2) monotonicity: $Y\succeq X$ implies $\rho(Y)\ge\rho(X)$.
--
--   Then $\rho$ is continuous on $\operatorname{int}(\operatorname{dom}\rho)$, and at every $\bar X\in\operatorname{int}(\operatorname{dom}\rho)$ it is subdifferentiable: there is a continuous linear functional $l\in\mathcal X^*$ with
--   $$\rho(X)\ge\rho(\bar X)+l(X-\bar X)\qquad\forall X\in\mathcal X.$$
--
--   The result says that for risk functions on spaces such as $\mathcal L_p$, convexity and monotonicity alone give continuity and the existence of subgradients wherever the function is finite in a neighbourhood, without any separate lower semicontinuity assumption.
--
--   **Formalization Note** The Banach lattice is abstract (Mathlib's `CompleteSpace`, `Lattice`, `HasSolidNorm`, `IsOrderedAddMonoid` on a real normed space), which includes the paper's function spaces with the pointwise order; this is a generalization. $\overline{\mathbb R}$ is `EReal` and continuity is with its order topology. The subdifferential consists of continuous linear functionals (`E →L[ℝ] ℝ`), i.e. $\mathcal Y:=\mathcal X^*$ as on p. 436. The interior of the domain may be empty, in which case the statement is vacuous, as on the page.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 437, Proposition 3.1

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
open Filter Topology

namespace ConvexRiskFn.Cont

theorem proposition_3_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]
    (ρ : E → EReal) (hρ : IsProper ρ) (h1 : ConvexRiskFn.Dual.A1 ρ) (h2 : A2 ρ) :
    ContinuousOn ρ (interior (ConvexRiskFn.Dual.dom ρ)) ∧
      ∀ Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ), (subdiff ρ Xbar).Nonempty := by sorry

end ConvexRiskFn.Cont
