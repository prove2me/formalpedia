-- Prove2me | Theorems.Thm_AdvanceSellDistress_eq_127_128
-- name    : AdvanceSellDistress.eq_127_128
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:17.903512+00:00
-- url     : https://prove2.me/theorems/7a295f34-9621-4975-ace3-05cd8ffa7159
-- title:
--   Proof of Proposition A.7, (127)–(128): under H, consumers buy coupons iff $E[u_{bb}]\ge\beta[e^*_B+(1-e^*_B)\lambda](v-1)$
-- statement:
--   Let $m_o=1$, $1<v<2$ and $I_l<I\le I_h$, under Assumptions 1–2. Let $(p_a,p_s)$ be a coupon plan of scheme H with $p_s\in[0,1]$ whose all-buy financing is secured with effort $e$. Then the inner consumers purchase in advance (Lemma A.1, with the deviation utilities of the all-or-nothing clause) if and only if
--   $$E[u_{bb}]=-p_a+\beta[e+(1-e)\lambda](v-p_s)\ \ge\ E[u_{ww}]=\beta[e^*_B+(1-e^*_B)\lambda](v-1),$$
--   where $e^*_B$ is the bank-only effort of Proposition 1(ii) (here $v_m=2$).
--
--   Under the all-or-nothing clause, a deviating consumer sends the game to pure bank financing, where she buys at the regular price $1$. The purchase constraint is therefore a single inequality against the bank-only surplus. This is the constraint that binds at the optimum of Proposition 10.
--
--   **Formalization Note** The left side is the model's purchase condition (`HPurchase`). $E[u_{ww}]$ is computed from the bank-only equilibrium relation, not assumed.
--
--   Differences from the source:
--   - reading: the steps of the proof of Proposition A.7 (general m_o, v ≤ 1 + m_o) → stated at m_o = 1, 1 < v < 2; reason: the proof of Proposition 10 (p. 51) is Proposition A.7 at m_o = 1, v ∈ (1,2); these milestones are the proof steps where Proposition 10 uses them (A.7's own claim p^u_s ∈ [0,1] fails for m_o > 1)
--   - reading: E[u_bw] = E[u_ww] (stated); E[u_wb] not stated → E[u_bw] = E[u_wb] = E[u_ww] = U_B; reason: under the all-or-nothing clause the campaign is refunded unless all consumers buy, so every deviation leads to the bank-only benchmark
--   - reading: p. 9 requires waiting to give "lower" utility → Lemma A.1's weak inequalities; reason: (127) and Lemma A.1 use ≥; the optimum of Proposition 10 binds the constraint
--   - encoding: 1 − β ∈ [0,1] → 0 < β ≤ 1; reason: the paper divides by β (I/β, 1/β − 1); β = 0 is excluded in every formula used
--   - encoding: k inner consumers of mass 1/k, k → ∞ (footnote 3) → a continuum: the mass valuing the service in state z is λ_z × segment mass; reason: the limit model of footnote 3; under the all-or-nothing clause the deviation utilities do not depend on k
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, proof of Proposition A.7, eqs. (127)–(128), p.78 (PDF 79)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model
import Definitions.Def_AdvanceSellDistress_ClosedForms

namespace AdvanceSellDistress

open Params

/-- **Eqs. (127)–(128)**, proof of Proposition A.7, Papanastasiou–Xiao–Yang, *Advance Selling to
Ease Financial Distress*, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, p. 78
(PDF 79), at `m_o = 1`, `1 < v < 2`, `I_l < I ≤ I_h`: under scheme "H", for a coupon plan
`(p_a, p_s)` with `p_s ∈ [0, 1]` whose all-buy financing is secured with effort `e`, the inner
consumers purchase in advance (Lemma A.1 with the all-or-nothing deviation utilities) if and only if
`E[u_bb] ≥ E[u_ww] = β [e*_B + (1 − e*_B) λ](v − 1)`.

**Formalization Note.** `m_o = 1` and `1 < v < 2` are the instance used by the proof of
Proposition 10 (p. 51); `e*_B` is the closed form of Proposition 1(ii) (`v_m = 2` here). -/
theorem eq_127_128 (P : Params) (hP : P.Standing) (hmo : P.mo = 1) (hv1 : 1 < P.v)
    (hv2 : P.v < 2) (hIl : P.Il < P.I) (hIh : P.I ≤ P.Ih)
    (pa ps e : ℝ) (hps : ps ∈ Set.Icc (0 : ℝ) 1) (hfin : ∃ D, P.HAllBuyOutcome pa ps D e) :
    P.HPurchase pa ps e ↔
      P.β * (P.eB + (1 - P.eB) * P.lam) * (P.v - 1) ≤ P.ubb pa ps e := by sorry

end AdvanceSellDistress
