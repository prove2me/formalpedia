-- Prove2me | Theorems.Thm_AdvanceSellDistress_eq_137_high_price_optimum
-- name    : AdvanceSellDistress.eq_137_high_price_optimum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:22.802849+00:00
-- url     : https://prove2.me/theorems/5ac6f102-f97c-40dd-8273-bda1d055bd0c
-- title:
--   Proof of Proposition A.7, Steps 2–3, (137): the high-price optimum of scheme H
-- statement:
--   Let $m_o=1$, $1<v<2$, $I_l<I\le I_h$ and $I_m<I$, under Assumptions 1–2, and suppose $v\ge\underline w^l_H=1+2\sqrt R/(1-\lambda)$, where $R=(1-\lambda)^2-2a(I/\beta-2\lambda)$. Put
--   $$p^{l*}_{sH}=v-1-\frac{\sqrt R}{1-\lambda},\qquad p^{l*}_{aH}=I-\beta\lambda(p^{l*}_{sH}+1),\qquad e^{l*}_H=\frac{(1-\lambda)(p^{l*}_{sH}+1)}{2a}.$$
--   Then:
--   1. the plan $(p^{l*}_{aH},p^{l*}_{sH})$ is feasible under scheme H with effort $e^{l*}_H$. It uses the high-price strategy $p_a=p^h_{bb}(p_s)$. Its profit is
--   $$\pi^{l*}_H=\beta a(e^{l*}_H)^2=\frac{\beta\Big[(1-\lambda)(2v-1+m_o)-\sqrt{(1-\lambda)^2(1+m_o)^2-8a[I/\beta-\lambda(1+m_o)]}\Big]^2}{16a};$$
--   2. every feasible plan with the high-price strategy $p_a\ge p^h_{bb}(p_s)$ earns at most $\pi^{l*}_H$.
--
--   This is the safe-loan side of the hybrid scheme's optimization. The consumers' purchase constraint binds, and the spot price is pushed as high as that constraint allows.
--
--   **Formalization Note** At $m_o=1$ the radicand in (137) equals $4R$. The paper's case condition $v\le\min\{1+m_o,\varphi^l_H(p^h_{bb}(1),1)\}$ holds automatically, since $1+m_o=2>v$ and $\varphi^l_H(p^h_{bb}(1),1)=2+\sqrt R/(1-\lambda)$. The paper's $p^{lh}_{sH}$ equals $p^{l*}_{sH}$.
--
--   Differences from the source:
--   - reading: the steps of the proof of Proposition A.7 (general m_o, v ≤ 1 + m_o) → stated at m_o = 1, 1 < v < 2; reason: the proof of Proposition 10 (p. 51) is Proposition A.7 at m_o = 1, v ∈ (1,2); these milestones are the proof steps where Proposition 10 uses them (A.7's own claim p^u_s ∈ [0,1] fails for m_o > 1)
--   - reading: the optimal spot price is p^{lh}_{sH} … the optimal coupon price is p^{lh}_{aH} … → the plan is feasible with the stated effort and profit, and no feasible high-price plan earns more; reason: "optimal" over the high-price plans (130)–(131)
--   - reading: plans with p_s ∈ [0,1], p_a ∈ ℝ → HPlan requires p_s ∈ [0,1], any real p_a; reason: the domain of (131)
--   - encoding: 1 − β ∈ [0,1] → 0 < β ≤ 1; reason: the paper divides by β (I/β, 1/β − 1); β = 0 is excluded in every formula used
--   - encoding: k inner consumers of mass 1/k, k → ∞ (footnote 3) → a continuum: the mass valuing the service in state z is λ_z × segment mass; reason: the limit model of footnote 3; under the all-or-nothing clause the deviation utilities do not depend on k
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, proof of Proposition A.7, Steps 2–3, case (1), eq. (137), pp.79–81 (PDF 80–82)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model
import Definitions.Def_AdvanceSellDistress_ClosedForms

namespace AdvanceSellDistress

open Params

/-- **Steps 2–3, eq. (137)**, proof of Proposition A.7, Papanastasiou–Xiao–Yang, *Advance Selling to
Ease Financial Distress*, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904,
pp. 79–81 (PDF 80–82), case (1), at `m_o = 1`, `1 < v < 2`, `I_m < I ≤ I_h`, `v ≥ w^l_H`: the plan
`(p^{l*}_{aH}, p^{l*}_{sH})` is feasible under scheme "H" with the high-price strategy
`p_a = p^h_bb(p_s)`, effort `e^{l*}_H` and profit
`π^{l*}_H = β[(1 − λ)(2v − 1 + m_o) − √((1 − λ)²(1 + m_o)² − 8a[I/β − λ(1 + m_o)])]² / (16a)`, and every
feasible plan with the high-price strategy `p_a ≥ p^h_bb(p_s)` earns at most this profit.

**Formalization Note.** `m_o = 1` and `1 < v < 2` as in the proof of Proposition 10 (p. 51). There
the paper's case condition `v ≤ min{1 + m_o, φ(p^h_bb(1), 1)}` holds because `1 + m_o = 2 > v` and
`φ(p^h_bb(1), 1) = 2 + √R/(1 − λ) ≥ 2`, and the paper's `p^{lh}_{sH}` equals `p^{l*}_{sH}`
(the radicand of (137) is `4R`). -/
theorem eq_137_high_price_optimum (P : Params) (hP : P.Standing) (hmo : P.mo = 1)
    (hv1 : 1 < P.v) (hv2 : P.v < 2) (hIl : P.Il < P.I) (hIm : P.Im < P.I) (hIh : P.I ≤ P.Ih)
    (hw : P.wH ≤ P.v) :
    P.HPlan P.paH P.psH P.eH P.piH ∧ P.paH = P.ph_bb P.psH ∧
    P.piH = P.β * ((1 - P.lam) * (2 * P.v - 1 + P.mo) -
        Real.sqrt ((1 - P.lam) ^ 2 * (1 + P.mo) ^ 2 -
          8 * P.a * (P.I / P.β - P.lam * (1 + P.mo)))) ^ 2 / (16 * P.a) ∧
    ∀ pa ps e π, P.HPlan pa ps e π → P.ph_bb ps ≤ pa → π ≤ P.piH := by sorry

end AdvanceSellDistress
