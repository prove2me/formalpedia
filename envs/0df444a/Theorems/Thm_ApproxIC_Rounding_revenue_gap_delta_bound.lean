-- Prove2me | Theorems.Thm_ApproxIC_Rounding_revenue_gap_delta_bound
-- name    : ApproxIC.Rounding.revenue_gap_delta_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:08.994275+00:00
-- url     : https://prove2.me/theorems/64b2114f-8ade-484f-a513-021f2379dbbf
-- title:
--   Appendix A, proof of Proposition 1, p. 38 — Π(m) − Π⋆(M(0)) ≤ δ/(1−δ)·Π⋆(M(0)) + ε/δ ≤ 2δΠ⋆(M(0)) + ε/δ
-- statement:
--   Let $\varepsilon>0$ and let $m\in\mathcal M(\varepsilon)$ be an $\varepsilon$-incentive compatible, individually rational mechanism. Then:
--
--   1. for every $\delta\in(0,1)$,
--   $$\Pi(m)-\Pi^\star(\mathcal M(0))\;\le\;\frac{\delta}{1-\delta}\,\Pi^\star(\mathcal M(0))+\frac{\varepsilon}{\delta};$$
--   2. for every $\delta\in(0,1/2]$,
--   $$\Pi(m)-\Pi^\star(\mathcal M(0))\;\le\;2\delta\,\Pi^\star(\mathcal M(0))+\frac{\varepsilon}{\delta}.$$
--
--   Here $\Pi(m)=\mathbb E_v[t(v)]$ is the revenue of $m$ and $\Pi^\star(\mathcal M(0))$ the optimal revenue over exactly incentive compatible, individually rational mechanisms.
--
--   This is the non-asymptotic form of Proposition 1: choosing $\delta=\sqrt\varepsilon$ gives a gain of order $\sqrt\varepsilon$.
--
--   **Formalization Note** No attainment hypothesis on the argmax of the rounding step is made: the inequality concerns only $m$ and $\delta$, and it remains true when the maximum over $S$ is not attained (the rounding can be carried out on the closure of the menu $\{(x(w),(1-\delta)t(w)):w\in S\}$, which is compact). Posing it without the hypothesis is therefore faithful and not weaker than the page.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 38, Appendix A, proof of Proposition 1, last display

import Mathlib
import Definitions.Def_ApproxIC_Rounding_Setting

namespace ApproxIC.Rounding

/-- Appendix A, proof of Proposition 1, p. 38: for every ε-IC mechanism `m` and every `δ ∈ (0,1)`,
`Π(m) − Π⋆(M(0)) ≤ δ/(1 − δ) · Π⋆(M(0)) + ε/δ`; for `δ ∈ (0, 1/2]` the right side is at most
`2δ · Π⋆(M(0)) + ε/δ`. -/
theorem revenue_gap_delta_bound (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε)
    (m : Mech) (hm : m ∈ Mset M ε) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      revenue M m - optRev M 0 ≤ δ / (1 - δ) * optRev M 0 + ε / δ) ∧
    (∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
      revenue M m - optRev M 0 ≤ 2 * δ * optRev M 0 + ε / δ) := by sorry

end ApproxIC.Rounding
