-- Prove2me | Theorems.Thm_ApproxIC_Rounding_rounded_mech_mem_M0
-- name    : ApproxIC.Rounding.rounded_mech_mem_M0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:35.121981+00:00
-- url     : https://prove2.me/theorems/eb6a1812-6bc9-42c0-a642-1e9addbeed64
-- title:
--   Appendix A, proof of Proposition 1, p. 38 — Nisan's rounded mechanism m̃ is exactly IC and IR: m̃ ∈ M(0)
-- statement:
--   Let $m=(x,t)\in\mathcal M(\varepsilon)$ be an $\varepsilon$-incentive compatible, individually rational mechanism for a buyer with values in $S=[0,\bar v]$, and let $\delta\in(0,1)$. Suppose $v^\star_\delta:S\to S$ selects, for each value $v\in S$, a maximizer
--   $$v^\star_\delta(v)\in\arg\max_{w\in S}\bigl\{\,v\cdot x(w)-(1-\delta)\,t(w)\,\bigr\}.$$
--   Define the **rounded mechanism** $\tilde m=(\tilde x,\tilde t)$ by
--   $$\tilde x(v)=x(v^\star_\delta(v)),\qquad \tilde t(v)=(1-\delta)\,t(v^\star_\delta(v))\qquad (v\in S),$$
--   and $\tilde x=\tilde t=0$ outside $S$. Then $\tilde m\in\mathcal M(0)$: it is well formed (in particular measurable), individually rational and exactly incentive compatible.
--
--   This is the first step of Nisan's rounding argument: discounting all payments by the factor $1-\delta$ and letting the buyer pick his favourite menu item turns an approximately incentive compatible mechanism into an exactly incentive compatible one.
--
--   **Formalization Note** The argmax is assumed attained, as on the page, through a selection map `vs` on $S$; it is unconstrained off $S$, which is why $\tilde m$ is set to $0$ there. The page says "$\tilde m$ is a 0-IC mechanism" and then uses $\tilde m\in\mathcal M(0)$ ("$\Pi^\star(\mathcal M(0))\ge\Pi(\tilde m)$"); the statement asserts membership in $\mathcal M(0)$, i.e. measurability, $\tilde x\in[0,1]$, IR and IC$_0$. Measurability of $\tilde m$ is part of the conclusion, not a hypothesis.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 38, Appendix A, proof of Proposition 1, first paragraph ("Therefore, m̃ is a 0-IC mechanism")

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting

namespace ApproxIC.Rounding

/-- Appendix A, proof of Proposition 1, p. 38: Nisan's rounding of an ε-IC mechanism. For
`δ ∈ (0,1)` and a selection `v⋆_δ(v) ∈ argmax_{w ∈ S} {v · x(w) − (1 − δ) t(w)}` (the map `vs`),
the mechanism `m̃ = (x(v⋆_δ(·)), (1 − δ) t(v⋆_δ(·)))`, set to `0` off `S = [0, v̄]`, is exactly
incentive compatible and individually rational, i.e. lies in `M(0)`. -/
theorem rounded_mech_mem_M0 (M : Model) (hM : M.Standing) (ε δ : ℝ) (m : Mech)
    (hm : m ∈ Mset M ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (vs : ℝ → ℝ)
    (hvs : ∀ v ∈ Set.Icc 0 M.vbar, vs v ∈ Set.Icc 0 M.vbar ∧
      ∀ w ∈ Set.Icc 0 M.vbar, v * m.x w - (1 - δ) * m.t w ≤ v * m.x (vs v) - (1 - δ) * m.t (vs v)) :
    (⟨(Set.Icc 0 M.vbar).indicator (fun v => m.x (vs v)),
      (Set.Icc 0 M.vbar).indicator (fun v => (1 - δ) * m.t (vs v))⟩ : Mech) ∈ Mset M 0 := by sorry

end ApproxIC.Rounding
