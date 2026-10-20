-- Prove2me | Theorems.Thm_ChainCompSI_Backfire_table_1_si
-- name    : ChainCompSI.Backfire.table_1_si
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:52.151758+00:00
-- url     : https://prove2.me/theorems/15bd4fe9-b0ee-4bdf-ad73-c796dd201fdc
-- title:
--   Table 1, left column, p. 9 — the strategic-inventory equilibrium for h ≤ 1/(4+θ)
-- statement:
--   Let $\theta > 0$ and $0 \le h \le 1/(4+\theta)$, i.e. $h(4+\theta) \le 1$. Then the strategic-inventory game has a passive-beliefs equilibrium, and in **every** equilibrium each chain $i$ has
--   $$w_{i1} = \frac{36 - 2h(4-\theta)}{68+19\theta}, \qquad p_{i1} = \frac{104 + 55\theta - 2h(1+\theta)(4-\theta)}{(2+\theta)(68+19\theta)},$$
--   $$D_{i1} = \frac{(1+\theta)(32 + 19\theta + 2h(4-\theta))}{(2+\theta)(68+19\theta)}, \qquad I_i = \frac{(1+\theta)(20+7\theta)(1 - h(4+\theta))}{(2+\theta)(68+19\theta)},$$
--   $$w_{i2} = \frac{24 + 40h + 14h\theta}{68+19\theta}, \qquad p_{i2} = \frac{92 + 43\theta + 2h(1+\theta)(20+7\theta)}{(2+\theta)(68+19\theta)},$$
--   $$D_{i2} = \frac{(1+\theta)(44 + 19\theta - 2h(20+7\theta))}{(2+\theta)(68+19\theta)},$$
--   and the manufacturer's equilibrium profit is
--   $$\Pi_i = \frac{4(1+\theta)\bigl(306 - 34h(4-\theta) + h^2(272 + \theta(136 + 21\theta))\bigr)}{(68+19\theta)^2}.$$
--   These closed forms are the basis of every comparison in §3 of the paper.
--
--   **Formalization Note** The retailer's profit $\pi_i$ is not stated: the page prints "see Online Appendix", which is not part of the source. It is determined by the definition of the realized retailer profit and the rows above. The claim covers every equilibrium profile, asymmetric ones included.
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), p. 9, Table 1, left column (SI, h ≤ 1/(4+θ))

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

namespace ChainCompSI.Backfire

theorem table_1_si (θ h : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (hcap : h * (4 + θ) ≤ 1) : (∃ E, IsEq θ h SI E) ∧ ∀ E, IsEq θ h SI E → ∀ i : Fin 2, E.w1 i = (36 - 2 * h * (4 - θ)) / (68 + 19 * θ) ∧ E.p1 i = (104 + 55 * θ - 2 * h * (1 + θ) * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ E.D1 θ i = (1 + θ) * (32 + 19 * θ + 2 * h * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ E.inv i = (1 + θ) * (20 + 7 * θ) * (1 - h * (4 + θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ E.w2' i = (24 + 40 * h + 14 * h * θ) / (68 + 19 * θ) ∧ E.p2' i = (92 + 43 * θ + 2 * h * (1 + θ) * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ E.D2 θ i = (1 + θ) * (44 + 19 * θ - 2 * h * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ)) ∧ mfrProfit θ E i = 4 * (1 + θ) * (306 - 34 * h * (4 - θ) + h ^ 2 * (272 + θ * (136 + 21 * θ))) / (68 + 19 * θ) ^ 2 := by sorry

end ChainCompSI.Backfire
