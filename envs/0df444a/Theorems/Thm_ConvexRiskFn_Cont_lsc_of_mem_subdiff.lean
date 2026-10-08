-- Prove2me | Theorems.Thm_ConvexRiskFn_Cont_lsc_of_mem_subdiff
-- name    : ConvexRiskFn.Cont.lsc_of_mem_subdiff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:47.859436+00:00
-- url     : https://prove2.me/theorems/49884b0e-c92f-42b2-bc13-97084b8963d8
-- title:
--   Proof of Proposition 3.1, p. 437 — if ∂ρ(X̄) contains a continuous l, then ρ is lower semicontinuous at X̄
-- statement:
--   Let $\mathcal X$ be a real normed space, $\rho:\mathcal X\to\overline{\mathbb R}$, $\bar X\in\mathcal X$, and let $l\in\mathcal X^*$ be a continuous linear functional with
--   $$\rho(X)\ge\rho(\bar X)+l(X-\bar X)\qquad\forall X\in\mathcal X,$$
--   i.e. $l\in\partial\rho(\bar X)$. Then $\rho$ is lower semicontinuous at $\bar X$.
--
--   In the proof of Proposition 3.1 this is the step "it follows then from (3.1) that $\rho$ is lower semicontinuous at $\bar X$".
--
--   **Formalization Note** Lower semicontinuity is Mathlib's `LowerSemicontinuousAt` for an `EReal`-valued function. The paper applies this at $\bar X\in\operatorname{int}(\operatorname{dom}\rho)$ for proper $\rho$; the statement needs no assumption on $\bar X$ or $\rho$ (if $\rho(\bar X)=\pm\infty$ the conclusion holds for elementary reasons), so it is stated without one.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 437, proof of Proposition 3.1: "Consequently, l is continuous, and hence l ∈ ∂ρ(X̄). It follows then from (3.1) that ρ is lower semicontinuous at X̄."

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
open Filter Topology

namespace ConvexRiskFn.Cont

theorem lsc_of_mem_subdiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (Xbar : E) (l : E →L[ℝ] ℝ) (hl : l ∈ subdiff ρ Xbar) :
    LowerSemicontinuousAt ρ Xbar := by sorry

end ConvexRiskFn.Cont
