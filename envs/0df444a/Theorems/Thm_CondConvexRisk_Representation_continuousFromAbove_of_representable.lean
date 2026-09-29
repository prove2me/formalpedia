-- Prove2me | Theorems.Thm_CondConvexRisk_Representation_continuousFromAbove_of_representable
-- name    : CondConvexRisk.Representation.continuousFromAbove_of_representable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:58:07.933022+00:00
-- url     : https://prove2.me/theorems/f3b94a29-14f3-4d88-9c17-9b0c1f9e3d9a
-- title:
--   Proof of Theorem 3.2, $b\Rightarrow a$ — representable implies continuous from above
-- statement:
--   Let $\rho:L^\infty\to L^\infty_{\mathcal G}$ be a conditional convex risk measure that is representable, i.e.
--   $$\rho(X)=\operatorname*{ess.sup}_{Q\in\mathcal P_{\mathcal G}}\{-E_Q(X\mid\mathcal G)-\alpha(Q)\},\qquad X\in L^\infty,$$
--   for some penalty $\alpha:\mathcal P_{\mathcal G}\to L^0_{\mathcal G}([0,+\infty])$. Then $\rho$ is continuous from above: $X_n,X\in L^\infty$ and $X_n\searrow X$ $P$-a.s. imply $\rho(X_n)\nearrow\rho(X)$ $P$-a.s.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 6, proof of Theorem 3.2, step b ⇒ a

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem continuousFromAbove_of_representable {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (hrep : IsRepresentable m P ρ) :
    IsContinuousFromAbove P ρ := by sorry

end CondConvexRisk.Representation
