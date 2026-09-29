-- Prove2me | Theorems.Thm_CondConvexRisk_Entropic_rhoGamma_continuousFromAbove
-- name    : CondConvexRisk.Entropic.rhoGamma_continuousFromAbove
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:02:22.349006+00:00
-- url     : https://prove2.me/theorems/7976a04a-75d8-43a3-a60e-00f276e41d2a
-- title:
--   Proof of Proposition 5.4, p. 13 — $\rho_\gamma$ is continuous from above
-- statement:
--   Let $\gamma>0$. If $X_n, X\in L^\infty$ and $X_n\searrow X$ $P$-a.s., then
--   $$\rho_\gamma(X_n)\nearrow\rho_\gamma(X)\qquad P\text{-a.s.},$$
--   where $\rho_\gamma(X)=\frac1\gamma\log E_P(e^{-\gamma X}\mid\mathcal G)$.
--
--   Continuity from above is condition (a) of the representation theorem (Theorem 3.2) and is the first step of the proof of Proposition 5.4.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 13, Proof of Proposition 5.4, first sentence

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem rhoGamma_continuousFromAbove {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    IsContinuousFromAbove P (rhoGamma m P γ) := by sorry

end CondConvexRisk.Entropic
