-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_lemma_1
-- name    : CrossLicensing.Innovation.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:01:21.264974+00:00
-- url     : https://prove2.me/theorems/876f271f-fda1-4df9-b812-0940c6a117e4
-- title:
--   Lemma 1, p. 12 — the supplier's optimal price induces a duopoly iff β ≥ √3 − 1 or T2 ≤ T̂2(T1|β); prices, profits and gross profits
-- statement:
--   Let $0 \le \beta \le 1$ and $0 \le T_1 \le T_2$. Let $r^*(T_1, T_2)$ be the least maximizer of the supplier's profit $r(q_1 + q_2)$ over $r \ge 0$, with $(q_1, q_2)$ the Cournot quantities at $r$. Let $\mathcal D$ be the condition
--   $$\beta \ge \sqrt3 - 1 \quad\text{or}\quad \big(\beta < \sqrt3 - 1 \text{ and } T_2 \le \hat T_2(T_1\mid\beta)\big),\qquad \hat T_2(T_1\mid\beta) = \frac{2 - \sqrt3 + T_1(1 - \beta(\sqrt3-1))}{\sqrt3 - 1 - \beta}.$$
--   Then:
--
--   1. the set of optimal prices has a least element, and it is $r^*(T_1, T_2)$;
--   2. if $\mathcal D$ holds, $r^* = r_d = \tfrac14(2 + (T_1+T_2)(1+\beta))$, both manufacturers sell a positive quantity (duopoly), the supplier's maximal profit over $r \ge 0$ is $\tfrac1{24}(2 + (T_1+T_2)(1+\beta))^2$, and the gross profits are $\Pi^*_1 = \tfrac1{144}((5\beta-7)T_1 + (5-7\beta)T_2 - 2)^2$ and $\Pi^*_2 = \tfrac1{144}((5\beta-7)T_2 + (5-7\beta)T_1 - 2)^2$;
--   3. if $\mathcal D$ fails, $r^* = r_m = \tfrac12(1 + T_1\beta + T_2)$, manufacturer 1 sells nothing while manufacturer 2 sells a positive quantity (monopoly), the supplier's maximal profit is $\tfrac18(1 + \beta T_1 + T_2)^2$, and $\Pi^*_1 = 0$, $\Pi^*_2 = \tfrac1{16}(\beta T_1 + T_2 + 1)^2$.
--
--   Lemma 1 resolves the supplier's pricing stage, and its gross profits are the payoffs of the innovation game.
--
--   **Formalization Note** "Optimal profit" is stated as the greatest element of the supplier's profits over $r \ge 0$ (attained). At $T_2 = \hat T_2(T_1\mid\beta)$ the supplier is indifferent between $r_d$ and $r_m$; the least-price rule, which defines $r^*$, picks $r_d$, matching the lemma's "$\le$".
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 12, Lemma 1; proof p. A.1 (PDF 33)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model
import Definitions.Def_CrossLicensing_Innovation_ClosedForms

namespace CrossLicensing.Innovation

theorem lemma_1 (β T1 T2 : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hT1 : 0 ≤ T1) (hT12 : T1 ≤ T2) :
    IsLeast (optimalPrices β T1 T2) (price β T1 T2) ∧
    ((Real.sqrt 3 - 1 ≤ β ∨ (β < Real.sqrt 3 - 1 ∧ T2 ≤ That2 β T1)) →
      price β T1 T2 = rd β T1 T2 ∧ IsDuopoly β T1 T2 ∧
      IsGreatest (supplierProfit β T1 T2 '' Set.Ici 0) ((2 + (T1 + T2) * (1 + β)) ^ 2 / 24) ∧
      grossProfit1 β T1 T2 = duoGross1 β T1 T2 ∧ grossProfit2 β T1 T2 = duoGross2 β T1 T2) ∧
    (¬ (Real.sqrt 3 - 1 ≤ β ∨ (β < Real.sqrt 3 - 1 ∧ T2 ≤ That2 β T1)) →
      price β T1 T2 = rm β T1 T2 ∧
      (quantities β T1 T2 (price β T1 T2)).1 = 0 ∧ 0 < (quantities β T1 T2 (price β T1 T2)).2 ∧
      IsGreatest (supplierProfit β T1 T2 '' Set.Ici 0) ((1 + β * T1 + T2) ^ 2 / 8) ∧
      grossProfit1 β T1 T2 = 0 ∧ grossProfit2 β T1 T2 = (β * T1 + T2 + 1) ^ 2 / 16) := by sorry

end CrossLicensing.Innovation
