-- Prove2me | Theorems.Thm_ApproxIC_Rounding_payment_loss_bound
-- name    : ApproxIC.Rounding.payment_loss_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:05.72431+00:00
-- url     : https://prove2.me/theorems/c058ea32-a501-4388-b115-9ca295cb538c
-- title:
--   Appendix A, proof of Proposition 1, p. 38 — rounding loses at most ε/δ of each payment: t(v′) ≥ t(v) − ε/δ
-- statement:
--   Let $m=(x,t)\in\mathcal M(\varepsilon)$ be an $\varepsilon$-incentive compatible, individually rational mechanism on $S=[0,\bar v]$, let $\delta\in(0,1)$, and let $v^\star_\delta:S\to S$ select maximizers
--   $$v^\star_\delta(v)\in\arg\max_{w\in S}\bigl\{\,v\cdot x(w)-(1-\delta)\,t(w)\,\bigr\}.$$
--   Then for every $v\in S$, with $v'=v^\star_\delta(v)$,
--   $$t(v')\;\ge\;t(v)-\frac{\varepsilon}{\delta}.$$
--
--   In words: the menu item chosen by type $v$ after the payments are discounted by $1-\delta$ charges at most $\varepsilon/\delta$ less than the item that type was originally assigned. This is the estimate that controls the revenue lost by Nisan's rounding.
--
--   **Formalization Note** The selection $v^\star_\delta$ is the map `vs`, assumed to take values in $S$ and to attain the maximum for each $v\in S$, as on the page.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 38, Appendix A, proof of Proposition 1, third display

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting

namespace ApproxIC.Rounding

/-- Appendix A, proof of Proposition 1, p. 38: for an ε-IC mechanism `m = (x, t)`, `δ ∈ (0,1)` and
`v′ = v⋆_δ(v) ∈ argmax_{w ∈ S} {v · x(w) − (1 − δ) t(w)}` (the map `vs`), one has
`t(v′) ≥ t(v) − ε/δ` for every `v ∈ S`. -/
theorem payment_loss_bound (M : Model) (hM : M.Standing) (ε δ : ℝ) (m : Mech)
    (hm : m ∈ Mset M ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (vs : ℝ → ℝ)
    (hvs : ∀ v ∈ Set.Icc 0 M.vbar, vs v ∈ Set.Icc 0 M.vbar ∧
      ∀ w ∈ Set.Icc 0 M.vbar, v * m.x w - (1 - δ) * m.t w ≤ v * m.x (vs v) - (1 - δ) * m.t (vs v)) :
    ∀ v ∈ Set.Icc 0 M.vbar, m.t v - ε / δ ≤ m.t (vs v) := by sorry

end ApproxIC.Rounding
