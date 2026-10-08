-- Prove2me | Theorems.Thm_ConvexRiskFn_Cont_exists_algSubgradient
-- name    : ConvexRiskFn.Cont.exists_algSubgradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:57.303091+00:00
-- url     : https://prove2.me/theorems/87085d0d-6c87-4787-9dc7-3d541030305a
-- title:
--   §3.1, pp. 436–437 — a proper convex ρ has an algebraic subgradient at every point of int(dom ρ)
-- statement:
--   Let $\mathcal X$ be a real normed space and $\rho:\mathcal X\to\overline{\mathbb R}$ a proper function satisfying (A1). If $\bar X\in\operatorname{int}(\operatorname{dom}\rho)$, then there is a linear functional $l:\mathcal X\to\mathbb R$ (not necessarily continuous) with
--   $$\rho(X)\ge\rho(\bar X)+l(X-\bar X)\qquad\forall X\in\mathcal X,$$
--   i.e. $l$ is an algebraic subgradient of $\rho$ at $\bar X$ in the sense of (3.1).
--
--   The paper uses this as the first step of Proposition 3.1; continuity of $l$ is what the lattice structure adds afterwards.
--
--   **Formalization Note** The functional is an arbitrary $\mathbb R$-linear map `E →ₗ[ℝ] ℝ`; no continuity is asserted.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), pp. 436–437, §3.1: "ρ always possesses an algebraic subgradient at any point X̄ ∈ int(dom ρ) (cf. Levin [11, Lemma 1.1])" and the Hahn–Banach sentence on p. 437

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
open Filter Topology

namespace ConvexRiskFn.Cont

theorem exists_algSubgradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → EReal) (hρ : IsProper ρ) (h1 : ConvexRiskFn.Dual.A1 ρ) (Xbar : E)
    (hXbar : Xbar ∈ interior (ConvexRiskFn.Dual.dom ρ)) :
    ∃ l : E →ₗ[ℝ] ℝ, IsAlgSubgradient ρ Xbar l := by sorry

end ConvexRiskFn.Cont
