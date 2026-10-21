-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_H_continuousOn
-- name    : EndoInvDemand.Clearing.H_continuousOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:51.337985+00:00
-- url     : https://prove2.me/theorems/7f4c42d8-0c9b-482a-951e-dbd79c635cd0
-- title:
--   Proof of Theorem 3.2, p. 31 — v ↦ H_Z(v) is continuous on dom H_Z
-- statement:
--   Let $R$ satisfy Assumption 3.1 on $\mathbb D\in\{\mathbb R,\mathbb R_{++}\}$, let the aggregate endowment $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. Then the pricing map
--   $$v\mapsto H_Z(v)=\frac{\mathbb E[Z\exp(-R(\mathcal X+Z-v))]}{\mathbb E[\exp(-R(\mathcal X+Z-v))]}$$
--   is continuous on its domain $\operatorname{dom}H_Z$.
--
--   Continuity is the first step of the existence proof (Theorem 3.2), which locates a fixed point by the intermediate value theorem, and of the closedness of the set of clearing prices.
--
--   **Formalization Note** For $\mathbb D=\mathbb R_{++}$, $\operatorname{dom}H_Z$ is $(-\infty,\operatorname{ess\,inf}[\mathcal X+Z]]$ or $(-\infty,\operatorname{ess\,inf}[\mathcal X+Z])$; continuity is relative to that set, so at its right end point (when it belongs to the domain) it is continuity from the left. $\operatorname{dom}H_Z$ requires a finite denominator (see the definitions item).
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, proof of Theorem 3.2 (Online Appendix D.1), p. 31, "We first note that R is continuous, and therefore so is v ↦ H_Z(v)."

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Proof of Theorem 3.2, p. 31: `v ↦ H_Z(v)` is continuous on `dom H_Z`. -/
theorem H_continuousOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (X Z : Ω → ℝ) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ContinuousOn (H P D R X Z) (domH P D R X Z) := by sorry

end EndoInvDemand.Clearing
