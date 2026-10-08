-- Prove2me | Theorems.Thm_ConvexRiskFn_Cont_continuousOn_of_lsc_interior
-- name    : ConvexRiskFn.Cont.continuousOn_of_lsc_interior
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:54.556144+00:00
-- url     : https://prove2.me/theorems/98884af0-1594-40e9-aafb-a4c9be31234b
-- title:
--   Phelps [19, Theorem 3.3], as used on p. 437 — a proper convex ρ on a Banach space, lsc on int(dom ρ), is continuous there
-- statement:
--   Let $\mathcal X$ be a real Banach space and $\rho:\mathcal X\to\overline{\mathbb R}$ a proper function satisfying (A1) (convexity). If $\rho$ is lower semicontinuous at every point of $\operatorname{int}(\operatorname{dom}\rho)$, then
--   $$\rho\ \text{is continuous on}\ \operatorname{int}(\operatorname{dom}\rho).$$
--
--   The proof of Proposition 3.1 cites this (Phelps, Convex Functions, Monotone Operators and Differentiability, Theorem 3.3) as its last step. Completeness of $\mathcal X$ is essential.
--
--   **Formalization Note** Continuity is `ContinuousOn` for an `EReal`-valued function with the order topology; on $\operatorname{int}(\operatorname{dom}\rho)$ the function is finite, so this is ordinary continuity of a real function. If the interior is empty the statement holds trivially, as on the page.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 437, proof of Proposition 3.1, last sentence (Phelps [19, Theorem 3.3])

import Mathlib
import Definitions.Def_ConvexRiskFn_Cont_Setting
open Filter Topology

namespace ConvexRiskFn.Cont

theorem continuousOn_of_lsc_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ρ : E → EReal) (hρ : IsProper ρ) (h1 : ConvexRiskFn.Dual.A1 ρ)
    (hlsc : ∀ X ∈ interior (ConvexRiskFn.Dual.dom ρ), LowerSemicontinuousAt ρ X) :
    ContinuousOn ρ (interior (ConvexRiskFn.Dual.dom ρ)) := by sorry

end ConvexRiskFn.Cont
