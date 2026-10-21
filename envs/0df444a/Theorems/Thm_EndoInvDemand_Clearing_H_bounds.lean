-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_H_bounds
-- name    : EndoInvDemand.Clearing.H_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:44.707962+00:00
-- url     : https://prove2.me/theorems/26d55ff2-fcea-4be1-ac8a-e0340add6462
-- title:
--   Proof of Theorem 3.2, p. 31 — ess inf Z ≤ H_Z(v) ≤ ess sup Z ∨ ess inf[𝒳 + Z] on dom H_Z
-- statement:
--   Let $R$ satisfy Assumption 3.1 on $\mathbb D\in\{\mathbb R,\mathbb R_{++}\}$, let $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. For every $v\in\operatorname{dom}H_Z$,
--   $$\operatorname{ess\,inf}Z\;\le\;H_Z(v)\;\le\;\operatorname{ess\,sup}Z\vee\operatorname{ess\,inf}[\mathcal X+Z].$$
--
--   These bounds make the set $V(Z)$ of clearing prices bounded, which together with closedness gives its compactness in Theorem 3.2; they also make the left limit inferior of $H_Z$ at $\operatorname{ess\,inf}[\mathcal X+Z]$ a finite number.
--
--   **Formalization Note** The upper bound is stated as printed, with the maximum $\operatorname{ess\,sup}Z\vee\operatorname{ess\,inf}[\mathcal X+Z]$, and not sharpened.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, proof of Theorem 3.2 (Online Appendix D.1), p. 31, last paragraph

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Proof of Theorem 3.2, p. 31: `ess inf Z ≤ H_Z(v) ≤ ess sup Z ∨ ess inf[𝒳 + Z]` for every
`v ∈ dom H_Z`. -/
theorem H_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (X Z : Ω → ℝ) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ∀ v ∈ domH P D R X Z,
      essInf Z P ≤ H P D R X Z v ∧ H P D R X Z v ≤ max (essSup Z P) (essInf (fun ω => X ω + Z ω) P) := by sorry

end EndoInvDemand.Clearing
