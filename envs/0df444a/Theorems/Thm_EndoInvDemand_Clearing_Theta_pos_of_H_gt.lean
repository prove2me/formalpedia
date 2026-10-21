-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_Theta_pos_of_H_gt
-- name    : EndoInvDemand.Clearing.Theta_pos_of_H_gt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:09.64112+00:00
-- url     : https://prove2.me/theorems/d2fdffd8-6d37-4a8a-b5b2-fc76303f0442
-- title:
--   Proof of Corollary 3.4, p. 33 — if H_Z(ess inf[𝒳+Z]) > ess inf[𝒳+Z] then Θ_Z > 0 on [ess inf Z, ess inf[𝒳+Z]]
-- statement:
--   Let $\mathbb D=\mathbb R_{++}$, let $R$ satisfy Assumption 3.1, let $\mathcal X$ satisfy Assumption 2.1, let $Z\in L^\infty$, and assume any of the conditions (a)–(d) of Theorem 3.3. Write $e=\operatorname{ess\,inf}[\mathcal X+Z]$. If $e\in\operatorname{dom}H_Z$ and $H_Z(e)>e$, then
--   $$\Theta_Z(v)=\mathbb E\big[(Z-v)\exp(-R(\mathcal X+Z-v))\big]>0\qquad\text{for every }v\in[\operatorname{ess\,inf}Z,\,e].$$
--
--   Since every clearing price lies in $[\operatorname{ess\,inf}Z,e]$, this shows that no clearing price exists when $H_Z(e)>e$: the necessity half of Corollary 3.4 in the case $e\in\operatorname{dom}H_Z$.
--
--   **Formalization Note** Every $v\le e$ lies in $\operatorname{dom}H_Z$ once $e$ does, so no separate membership hypothesis is stated for $v$.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, proof of Corollary 3.4 (Online Appendix D.3), p. 33, second paragraph

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Proof of Corollary 3.4, p. 33: for `𝔻 = ℝ₊₊` under any condition of Theorem 3.3, if
`ess inf[𝒳 + Z] ∈ dom H_Z` and `H_Z(ess inf[𝒳 + Z]) > ess inf[𝒳 + Z]`, then `Θ_Z(v) > 0` for every
`v ∈ [ess inf Z, ess inf[𝒳 + Z]]`. -/
theorem Theta_pos_of_H_gt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ → ℝ) (hR : Assumption31 .pos R)
    (X Z : Ω → ℝ) (hX : Assumption21 P .pos X) (hZ : MemLp Z ⊤ P)
    (hcond : Thm33Cond P .pos R X Z)
    (he : (essInf (fun ω => X ω + Z ω) P) ∈ domH P .pos R X Z)
    (hgt : essInf (fun ω => X ω + Z ω) P < H P .pos R X Z (essInf (fun ω => X ω + Z ω) P)) :
    ∀ v ∈ Set.Icc (essInf Z P) (essInf (fun ω => X ω + Z ω) P), 0 < Theta P .pos R X Z v := by sorry

end EndoInvDemand.Clearing
