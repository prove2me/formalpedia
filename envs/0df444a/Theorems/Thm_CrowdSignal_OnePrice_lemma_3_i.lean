-- Prove2me | Theorems.Thm_CrowdSignal_OnePrice_lemma_3_i
-- name    : CrowdSignal.OnePrice.lemma_3_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:01.412224+00:00
-- url     : https://prove2.me/theorems/19c2bda5-05f5-4dd7-ba38-38a047ee0ae9
-- title:
--   Lemma 3(i): two low-type mimicking indifference prices
-- statement:
--   Under the standing parameter restrictions and $T\le\bar p_1$, let $p^{L*}_1=(3+\alpha)q_L/8$ and let $\pi^{L*}$ be the maximum profit of the low type when believed low. There is an upper price $\bar p'_1$ with
--   $$\bar p_1<p^{L*}_1<\bar p'_1\le q_H,$$
--   such that, among feasible prices no greater than $q_H$, the low type's profit when believed high equals $\pi^{L*}$ exactly at $\bar p_1$ and $\bar p'_1$.
--
--   These are the two prices at which mimicking leaves the low type indifferent to revealing its quality.
--
--   **Formalization Note** The printed lemma's circular preamble involving $\underline p_1$ is read in the financing regime used by Proposition 1, $T\le\bar p_1$. The lower root is the displayed closed form from Proposition 1, rather than a chosen witness.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 18, Lemma 3(i)

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CrowdSignal.OnePrice

/-- Lemma 3(i): the two low-type mimicking indifference prices. -/
theorem lemma_3_i (P : Params) (hP : P.Standing) (hT : P.T ≤ pbar P) :
    ∃ pbar',
      pbar P < (3 + P.α) / 8 * P.qL ∧
      (3 + P.α) / 8 * P.qL < pbar' ∧
      pbar' ≤ P.qH ∧
      ∀ p, P.T ≤ p → p ≤ P.qH →
        (profit P P.qL P.qH p = optProfit P P.qL P.qL ↔
          p = pbar P ∨ p = pbar') := by sorry

end CrowdSignal.OnePrice
