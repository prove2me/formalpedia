-- Prove2me | Theorems.Thm_CondConvexRisk_Entropic_rhoGamma_isCondConvexRiskMeasure
-- name    : CondConvexRisk.Entropic.rhoGamma_isCondConvexRiskMeasure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:01:06.906781+00:00
-- url     : https://prove2.me/theorems/3190aa9b-6f08-4359-8f66-29ea49508928
-- title:
--   Section 5, p. 12 — $\rho_\gamma$ is a conditional convex risk measure
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\mathcal G\subseteq\mathcal F$ a sub-$\sigma$-algebra and $\gamma>0$. The map
--   $$\rho_\gamma(X)=\frac1\gamma\log E_P\big(e^{-\gamma X}\mid\mathcal G\big),\qquad X\in L^\infty,$$
--   is a conditional convex risk measure: it maps $L^\infty$ into $L^\infty_{\mathcal G}$, is translation invariant with respect to $\mathcal G$-measurable bounded shifts, monotone, conditionally convex and satisfies $\rho_\gamma(0)=0$.
--
--   This is the claim of Section 5 that the acceptance set $A_\gamma$ "leads to a conditional convex risk measure" with this explicit form.
--
--   **Formalization Note** All properties hold $P$-a.s.; $\rho_\gamma$ must also be well defined on $P$-classes and return a $\mathcal G$-measurable function.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 12, Section 5 (display defining A_γ and ρ_γ; Definition 5.2)

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem rhoGamma_isCondConvexRiskMeasure {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    IsCondConvexRiskMeasure m P (rhoGamma m P γ) := by sorry

end CondConvexRisk.Entropic
