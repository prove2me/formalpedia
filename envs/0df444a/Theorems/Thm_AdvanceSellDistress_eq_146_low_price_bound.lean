-- Prove2me | Theorems.Thm_AdvanceSellDistress_eq_146_low_price_bound
-- name    : AdvanceSellDistress.eq_146_low_price_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:13.885789+00:00
-- url     : https://prove2.me/theorems/975cb966-84af-40e3-ac45-cf67f650e5c6
-- title:
--   Proof of Proposition A.7, low-price strategy, (146): risky-loan H plans have supremum profit equal to (137)
-- statement:
--   Let $m_o=1$, $1<v<2$, $I_l<I\le I_h$ and $I_m<I$, under Assumptions 1–2, and suppose $v\ge\underline w^l_H$. Then the least upper bound of the profits of the feasible plans of scheme H with the low-price strategy $p_a<p^h_{bb}(p_s)$ (a risky bank loan) is
--   $$\pi^{ll}_H=\frac{\beta\Big[(1-\lambda)(2v-1+m_o)-\sqrt{(1-\lambda)^2(1+m_o)^2-8a[I/\beta-\lambda(1+m_o)]}\Big]^2}{16a}.$$
--
--   Combined with (137), this shows that the risky-loan plans cannot beat the safe-loan optimum. The hybrid optimum's profit is therefore the same whichever loan regime is used.
--
--   **Formalization Note** The set consists of the profits $\pi$ of all $(p_a,p_s,e)$ with `HPlan` and $p_a<p^h_{bb}(p_s)$. The statement is `IsLUB`: an upper bound, approached by feasible plans.
--
--   Differences from the source:
--   - reading: the steps of the proof of Proposition A.7 (general m_o, v ≤ 1 + m_o) → stated at m_o = 1, 1 < v < 2; reason: the proof of Proposition 10 (p. 51) is Proposition A.7 at m_o = 1, v ∈ (1,2); these milestones are the proof steps where Proposition 10 uses them (A.7's own claim p^u_s ∈ [0,1] fails for m_o > 1)
--   - reading: the firm's maximum profit with low-price strategy is π^{ll}_H → π^{ll}_H is the least upper bound (IsLUB) of the low-price profits; reason: the maximizer (145) of the paper's case (ii) has p_a = p^h_bb(p_s), outside the low-price set p_a < p^h_bb(p_s), so the printed maximum need not be attained there
--   - reading: plans with p_s ∈ [0,1], p_a ∈ ℝ → HPlan requires p_s ∈ [0,1], any real p_a; reason: the domain of (131) and (143)
--   - encoding: 1 − β ∈ [0,1] → 0 < β ≤ 1; reason: the paper divides by β (I/β, 1/β − 1); β = 0 is excluded in every formula used
--   - encoding: k inner consumers of mass 1/k, k → ∞ (footnote 3) → a continuum: the mass valuing the service in state z is λ_z × segment mass; reason: the limit model of footnote 3; under the all-or-nothing clause the deviation utilities do not depend on k
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, proof of Proposition A.7, low-price strategy, eqs. (142)–(146), pp.82–85 (PDF 83–86)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model
import Definitions.Def_AdvanceSellDistress_ClosedForms

namespace AdvanceSellDistress

open Params

/-- **Eq. (146)**, proof of Proposition A.7 (low-price strategy), Papanastasiou–Xiao–Yang, *Advance
Selling to Ease Financial Distress*, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904,
pp. 82–85 (PDF 83–86), case (1), at `m_o = 1`, `1 < v < 2`, `I_m < I ≤ I_h`, `v ≥ w^l_H`: the
supremum of the profits of the feasible plans of scheme "H" with the low-price strategy
`p_a < p^h_bb(p_s)` is
`π^{ll}_H = β[(1 − λ)(2v − 1 + m_o) − √((1 − λ)²(1 + m_o)² − 8a[I/β − λ(1 + m_o)])]² / (16a)`.

**Formalization Note.** The paper's "maximum profit" is read as the least upper bound (`IsLUB`):
the maximizer (145) of the paper's case (ii) sits at `p_a = p^h_bb(p_s)`, outside the low-price set.
`m_o = 1` and `1 < v < 2` as in the proof of Proposition 10 (p. 51). -/
theorem eq_146_low_price_bound (P : Params) (hP : P.Standing) (hmo : P.mo = 1)
    (hv1 : 1 < P.v) (hv2 : P.v < 2) (hIl : P.Il < P.I) (hIm : P.Im < P.I) (hIh : P.I ≤ P.Ih)
    (hw : P.wH ≤ P.v) :
    IsLUB {π | ∃ pa ps e, P.HPlan pa ps e π ∧ pa < P.ph_bb ps}
      (P.β * ((1 - P.lam) * (2 * P.v - 1 + P.mo) -
        Real.sqrt ((1 - P.lam) ^ 2 * (1 + P.mo) ^ 2 -
          8 * P.a * (P.I / P.β - P.lam * (1 + P.mo)))) ^ 2 / (16 * P.a)) := by sorry

end AdvanceSellDistress
