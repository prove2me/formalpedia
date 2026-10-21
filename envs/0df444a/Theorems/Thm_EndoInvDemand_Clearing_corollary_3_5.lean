-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_corollary_3_5
-- name    : EndoInvDemand.Clearing.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:58.607502+00:00
-- url     : https://prove2.me/theorems/2e108370-23ad-402f-8b8d-558c0f4e72fa
-- title:
--   Corollary 3.5, p. 10 — 𝔻 = ℝ₊₊ and 𝔼[exp(−R(𝒳 + Z − ess inf[𝒳 + Z]))] = ∞ imply V(Z) ≠ ∅
-- statement:
--   Let $\mathbb D=\mathbb R_{++}$, let $R$ satisfy Assumption 3.1, let $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. If
--   $$\mathbb E\big[\exp\big(-R(\mathcal X+Z-\operatorname{ess\,inf}[\mathcal X+Z])\big)\big]=\infty,\tag{3.3}$$
--   then $Z\in\operatorname{dom}V$, that is, $V(Z)\neq\emptyset$.
--
--   This gives a clearing price without evaluating $H_Z$ at $\operatorname{ess\,inf}[\mathcal X+Z]$; for instance it applies when $\mathbb P(\mathcal X+Z=\operatorname{ess\,inf}[\mathcal X+Z])>0$ and $\lim_{z\searrow0}R(z)=-\infty$.
--
--   **Formalization Note** The expectation in (3.3) is a lower Lebesgue integral in $[0,\infty]$, with $\exp(-R(0))=\lim_{z\searrow0}\exp(-R(z))$ at the points where $\mathcal X+Z$ equals its essential infimum. "$Z\in\operatorname{dom}V$" means $V(Z)\ne\emptyset$ (§3.2). No condition of Theorem 3.3 is assumed, as on the page.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, Corollary 3.5 and (3.3), p. 10

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Corollary 3.5, p. 10: for `𝔻 = ℝ₊₊`, if `𝔼[exp(−R(𝒳 + Z − ess inf[𝒳 + Z]))] = ∞` (3.3),
then `Z ∈ dom V`, i.e. `V(Z) ≠ ∅`. -/
theorem corollary_3_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ → ℝ) (hR : Assumption31 .pos R)
    (X Z : Ω → ℝ) (hX : Assumption21 P .pos X) (hZ : MemLp Z ⊤ P) :
    denom P .pos R X Z (essInf (fun ω => X ω + Z ω) P) = ⊤ → (V P .pos R X Z).Nonempty := by sorry

end EndoInvDemand.Clearing
