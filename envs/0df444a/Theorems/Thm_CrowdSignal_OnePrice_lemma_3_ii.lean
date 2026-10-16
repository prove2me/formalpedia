-- Prove2me | Theorems.Thm_CrowdSignal_OnePrice_lemma_3_ii
-- name    : CrowdSignal.OnePrice.lemma_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:00.867024+00:00
-- url     : https://prove2.me/theorems/8af3e97f-95b8-4d34-8e37-180a22bdec12
-- title:
--   Lemma 3(ii): upper high-type indifference price
-- statement:
--   Under the standing parameter restrictions and $T\le\bar p_1$, let $p^{HL*}_1=\max\{[4q_L-(1-\alpha)q_H]/8,T\}$ and let $\pi^{HL*}$ be the maximum profit of the high type when believed low. There is exactly one price $\underline p'_1$ in $(p^{HL*}_1,q_H]$ such that
--   $$\pi^H(\underline p'_1)=\pi^{HL*}.$$
--   This upper crossing bounds the high type's prices that can sustain separation.
--
--   **Formalization Note** The lower barred threshold named in the printed preamble need not lie above $T$, so the statement characterizes the upper root that the proposition uses.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 18, Lemma 3(ii)

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CrowdSignal.OnePrice

/-- Lemma 3(ii): the upper high-type indifference price. -/
theorem lemma_3_ii (P : Params) (hP : P.Standing) (hT : P.T ≤ pbar P) :
    ∃! punder' : ℝ,
      max ((4 * P.qL - (1 - P.α) * P.qH) / 8) P.T < punder' ∧
      punder' ≤ P.qH ∧
      profit P P.qH P.qH punder' = optProfit P P.qH P.qL := by sorry

end CrowdSignal.OnePrice
