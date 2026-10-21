-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_Theta_neg_of_gt_root_of_c_or_d
-- name    : EndoInvDemand.Clearing.Theta_neg_of_gt_root_of_c_or_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:51.770727+00:00
-- url     : https://prove2.me/theorems/f0057042-a614-4d2f-9746-2b342c3f69d8
-- title:
--   Proof of Theorem 3.3 (c)–(d), p. 32 — under (c) or (d), Θ_Z < 0 on dom H_Z beyond any root
-- statement:
--   Let $R$ satisfy Assumption 3.1 on $\mathbb D\in\{\mathbb R,\mathbb R_{++}\}$, let $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. Assume either
--
--   (c) $z\in\mathbb R_{++}\mapsto z\exp(-R(\mathcal X+z))$ is almost surely non-decreasing, or
--   (d) $z\in\mathbb R_{++}\mapsto z\exp(-R(\mathcal X+z))$ is almost surely concave.
--
--   If $v_1\in\operatorname{dom}H_Z$ is a root, $\Theta_Z(v_1)=0$, then
--   $$\Theta_Z(v)<0\qquad\text{for every }v\in\operatorname{dom}H_Z\text{ with }v>v_1.$$
--
--   Hence $\Theta_Z$ has at most one root on $\operatorname{dom}H_Z$, which is the uniqueness argument of Theorem 3.3 under (c) or (d).
--
--   **Formalization Note** The paper argues that $\frac{\partial}{\partial v}\Theta_Z(v)<0$ for feasible $v$ at and beyond a root, after disposing of the case of a constant $Z$ separately; the formal statement is the consequence used (strict negativity beyond a root), and it covers the constant case too, so no case hypothesis is added.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, proof of Theorem 3.3 (Online Appendix D.2), p. 32, cases (c) and (d)

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Proof of Theorem 3.3 (c)–(d), p. 32: under condition (c) or (d), `Θ_Z` is strictly negative
on `dom H_Z` beyond any of its roots. -/
theorem Theta_neg_of_gt_root_of_c_or_d {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (X Z : Ω → ℝ) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    (h : condC P R X ∨ condD P R X) :
    ∀ v₁ ∈ domH P D R X Z, Theta P D R X Z v₁ = 0 →
      ∀ v ∈ domH P D R X Z, v₁ < v → Theta P D R X Z v < 0 := by sorry

end EndoInvDemand.Clearing
