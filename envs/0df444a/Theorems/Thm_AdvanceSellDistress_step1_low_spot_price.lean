-- Prove2me | Theorems.Thm_AdvanceSellDistress_step1_low_spot_price
-- name    : AdvanceSellDistress.step1_low_spot_price
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:23.172025+00:00
-- url     : https://prove2.me/theorems/9531c5c9-7d65-4f65-a062-cc072b278ebf
-- title:
--   Proof of Proposition A.7, Step 1, (132)–(134): high-price H plans with $p_s\le p^u_s$ never beat $\pi^*_B$
-- statement:
--   Let $m_o=1$, $1<v<2$ and $I_l<I\le I_h$, under Assumptions 1–2, and let
--   $$p^u_s=\frac{\sqrt{(1-\lambda)^2-2a(I/\beta-2\lambda)}}{1-\lambda}.$$
--   Every feasible plan $(p_a,p_s)$ of scheme H with $p_s\le p^u_s$ and $p_a\ge p^h_{bb}(p_s)=I-\beta\lambda(p_s+1)$ (the high-price strategy) earns at most the bank-only profit:
--   $$\pi\le\pi^*_B=\beta a(e^*_B)^2 .$$
--
--   At $p_s=p^u_s$ the high-price effort equals the bank-only effort $e^*_B$. Below it, either the consumers refuse the coupon or the firm earns no more than with the bank alone. So an optimal hybrid plan uses a spot price above $p^u_s$.
--
--   **Formalization Note** A feasible plan is `HPlan`: secured all-buy financing with best-response effort, and the consumers' Lemma A.1 condition. $\pi^*_B$ is the closed form of Proposition 1(ii) (here $v_m=2$).
--
--   Differences from the source:
--   - reading: the steps of the proof of Proposition A.7 (general m_o, v ≤ 1 + m_o) → stated at m_o = 1, 1 < v < 2; reason: the proof of Proposition 10 (p. 51) is Proposition A.7 at m_o = 1, v ∈ (1,2); these milestones are the proof steps where Proposition 10 uses them (A.7's own claim p^u_s ∈ [0,1] fails for m_o > 1)
--   - reading: the firm is either unable or unwilling to advance sell by choosing p_s ∈ [0, p^u_s] → every feasible high-price plan with p_s ≤ p^u_s has profit ≤ π*_B; reason: "unable" means no feasible plan, "unwilling" means profit ≤ π*_B; Step 1 is part of the high-price analysis (130)–(131)
--   - reading: plans with p_s ∈ [0,1], p_a ∈ ℝ → HPlan requires p_s ∈ [0,1], any real p_a; reason: the domain of (131)
--   - encoding: 1 − β ∈ [0,1] → 0 < β ≤ 1; reason: the paper divides by β (I/β, 1/β − 1); β = 0 is excluded in every formula used
--   - encoding: k inner consumers of mass 1/k, k → ∞ (footnote 3) → a continuum: the mass valuing the service in state z is λ_z × segment mass; reason: the limit model of footnote 3; under the all-or-nothing clause the deviation utilities do not depend on k
-- source:
--   Papanastasiou–Xiao–Yang, Advance Selling to Ease Financial Distress, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904, proof of Proposition A.7, Step 1, eqs. (132)–(134), p.79 (PDF 80)

import Mathlib
import Definitions.Def_AdvanceSellDistress_Model
import Definitions.Def_AdvanceSellDistress_ClosedForms

namespace AdvanceSellDistress

open Params

/-- **Step 1, eqs. (132)–(134)**, proof of Proposition A.7, Papanastasiou–Xiao–Yang, *Advance
Selling to Ease Financial Distress*, Management Science 71(4) (2025), doi:10.1287/mnsc.2020.03904,
p. 79 (PDF 80), at `m_o = 1`, `1 < v < 2`, `I_l < I ≤ I_h`: with `p^u_s = √R / (1 − λ)`, every
feasible plan of scheme "H" with a low spot price `p_s ≤ p^u_s` and the high-price strategy
`p_a ≥ p^h_bb(p_s)` earns at most the bank-only profit `π*_B = β a (e*_B)²` — "the firm is either
unable or unwilling to advance sell by choosing p_s ∈ [0, p^u_s]".

**Formalization Note.** `m_o = 1` and `1 < v < 2` as in the proof of Proposition 10 (p. 51). -/
theorem step1_low_spot_price (P : Params) (hP : P.Standing) (hmo : P.mo = 1) (hv1 : 1 < P.v)
    (hv2 : P.v < 2) (hIl : P.Il < P.I) (hIh : P.I ≤ P.Ih) :
    ∀ pa ps e π, P.HPlan pa ps e π → ps ≤ P.pu → P.ph_bb ps ≤ pa → π ≤ P.piB := by sorry

end AdvanceSellDistress
