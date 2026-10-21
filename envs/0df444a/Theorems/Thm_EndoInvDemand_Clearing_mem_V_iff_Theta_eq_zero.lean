-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_mem_V_iff_Theta_eq_zero
-- name    : EndoInvDemand.Clearing.mem_V_iff_Theta_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:46.350022+00:00
-- url     : https://prove2.me/theorems/3f211244-8c33-4407-ab3f-ef9a883f007c
-- title:
--   Proof of Theorem 3.3, p. 32 — v = H_Z(v) iff Θ_Z(v) = 0, for v ∈ dom H_Z
-- statement:
--   Let $R$ satisfy Assumption 3.1 on $\mathbb D\in\{\mathbb R,\mathbb R_{++}\}$, let $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. For every $v\in\operatorname{dom}H_Z$,
--   $$v=H_Z(v)\iff\Theta_Z(v):=\mathbb E\big[(Z-v)\exp(-R(\mathcal X+Z-v))\big]=0.$$
--
--   The fixed-point equation is thereby turned into a root-finding problem for $\Theta_Z$, whose shape is controlled under conditions (c) and (d) of Theorem 3.3.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, proof of Theorem 3.3 (Online Appendix D.2), p. 32

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Proof of Theorem 3.3, p. 32: for `v ∈ dom H_Z`, `v = H_Z(v)` iff
`Θ_Z(v) = 𝔼[(Z − v) exp(−R(𝒳 + Z − v))] = 0`. -/
theorem mem_V_iff_Theta_eq_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (X Z : Ω → ℝ) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ∀ v ∈ domH P D R X Z, v = H P D R X Z v ↔ Theta P D R X Z v = 0 := by sorry

end EndoInvDemand.Clearing
