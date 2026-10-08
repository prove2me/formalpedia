-- Prove2me | Theorems.Thm_ConvexRiskFn_Cont_algSubgradient_nonneg
-- name    : ConvexRiskFn.Cont.algSubgradient_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:09.11498+00:00
-- url     : https://prove2.me/theorems/7702e89d-ae0b-4110-964f-7ac4cbbd4efc
-- title:
--   Proof of Proposition 3.1, p. 437 — under (A2), an algebraic subgradient is positive: l(X) ≥ 0 for X ∈ 𝒳₊
-- statement:
--   Let $\mathcal X$ be a real vector space with a partial order compatible with addition, and let $\rho:\mathcal X\to\overline{\mathbb R}$ satisfy (A2) (monotonicity). Let $\bar X\in\operatorname{dom}\rho$ with $\rho(\bar X)>-\infty$, and let $l$ be an algebraic subgradient of $\rho$ at $\bar X$, i.e. $\rho(X)\ge\rho(\bar X)+l(X-\bar X)$ for all $X$. Then $l$ is positive:
--   $$l(X)\ge0\qquad\text{for all }X\in\mathcal X_+=\{X: X\succeq0\}.$$
--
--   This is the step of the proof of Proposition 3.1 where monotonicity enters.
--
--   **Formalization Note** The paper takes $\bar X\in\operatorname{int}(\operatorname{dom}\rho)$ with $\rho$ proper; the statement only needs that $\rho(\bar X)$ is finite ($\bar X\in\operatorname{dom}\rho$ and $\rho(\bar X)>-\infty$), which is the situation of the paper. No topology is needed.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 437, proof of Proposition 3.1, second and third sentences

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
open Filter Topology

namespace ConvexRiskFn.Cont

theorem algSubgradient_nonneg {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] (ρ : E → EReal) (h2 : A2 ρ) (Xbar : E)
    (hdom : Xbar ∈ ConvexRiskFn.Dual.dom ρ) (hbot : ⊥ < ρ Xbar) (l : E →ₗ[ℝ] ℝ)
    (hl : IsAlgSubgradient ρ Xbar l) :
    ∀ X : E, 0 ≤ X → 0 ≤ l X := by sorry

end ConvexRiskFn.Cont
