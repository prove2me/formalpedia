-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_corollary_3_4
-- name    : EndoInvDemand.Clearing.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:03.896529+00:00
-- url     : https://prove2.me/theorems/944a0b97-d8df-4e9f-9ab3-873ac4dcc1cf
-- title:
--   Corollary 3.4, p. 10 — 𝔻 = ℝ₊₊ and (a)–(d): |V(Z)| = 1 iff H_Z(e) ≤ e (e ∈ dom H_Z) or liminf_{v↗e} H_Z(v) < e (e ∉ dom H_Z), e = ess inf[𝒳+Z]; V(Z) ≤ e
-- statement:
--   Let $\mathbb D=\mathbb R_{++}$, let $R$ satisfy Assumption 3.1, let the aggregate endowment $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. Assume that any of the conditions (a)–(d) of Theorem 3.3 holds. Write $e=\operatorname{ess\,inf}[\mathcal X+Z]$. Then:
--
--   1. There is exactly one clearing price, $|V(Z)|=1$, if and only if
--   $$\Big(e\in\operatorname{dom}H_Z\ \text{and}\ H_Z(e)\le e\Big)\quad\text{or}\quad\Big(e\notin\operatorname{dom}H_Z\ \text{and}\ \liminf_{v\nearrow e}H_Z(v)<e\Big).$$
--   2. Every clearing price is bounded above by $e$: $v\le e$ for all $v\in V(Z)$.
--
--   This is the paper's main existence-and-uniqueness result for the price of a liquidated claim when utilities live on the half line: under the uniqueness conditions of Theorem 3.3, the sufficient condition for existence of Theorem 3.2 is also necessary, and the clearing price never exceeds the worst-case aggregate wealth after liquidation.
--
--   **Formalization Note** $\liminf_{v\nearrow e}$ is the limit inferior along the left neighbourhood filter of $e$; $H_Z$ is bounded on $(-\infty,e)$, so it is a genuine limit inferior. $\operatorname{dom}H_Z$ requires a finite denominator $\mathbb E[\exp(-R(\mathcal X+Z-v))]$ (the page's "$>0$" always holds); in particular $e\notin\operatorname{dom}H_Z$ means that this expectation is $+\infty$ at $v=e$. The second sentence is stated for every element of $V(Z)$; for the unique solution it is the page's claim.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, Corollary 3.4, p. 10

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Corollary 3.4, p. 10: for `𝔻 = ℝ₊₊` under any condition of Theorem 3.3, `|V(Z)| = 1` iff
`H_Z(ess inf[𝒳 + Z]) ≤ ess inf[𝒳 + Z]` when `ess inf[𝒳 + Z] ∈ dom H_Z`, or
`liminf_{v ↗ ess inf[𝒳 + Z]} H_Z(v) < ess inf[𝒳 + Z]` when `ess inf[𝒳 + Z] ∉ dom H_Z`;
furthermore `V(Z) ≤ ess inf[𝒳 + Z]`. -/
theorem corollary_3_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ → ℝ) (hR : Assumption31 .pos R)
    (X Z : Ω → ℝ) (hX : Assumption21 P .pos X) (hZ : MemLp Z ⊤ P)
    (hcond : Thm33Cond P .pos R X Z) :
    ((∃! v, v ∈ V P .pos R X Z) ↔
        ((essInf (fun ω => X ω + Z ω) P) ∈ domH P .pos R X Z ∧ H P .pos R X Z (essInf (fun ω => X ω + Z ω) P) ≤ essInf (fun ω => X ω + Z ω) P ∨
          (essInf (fun ω => X ω + Z ω) P) ∉ domH P .pos R X Z ∧
            Filter.liminf (H P .pos R X Z) (𝓝[<] (essInf (fun ω => X ω + Z ω) P)) < essInf (fun ω => X ω + Z ω) P)) ∧
    ∀ v ∈ V P .pos R X Z, v ≤ essInf (fun ω => X ω + Z ω) P := by sorry

end EndoInvDemand.Clearing
