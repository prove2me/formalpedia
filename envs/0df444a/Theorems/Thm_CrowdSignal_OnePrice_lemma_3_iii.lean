-- Prove2me | Theorems.Thm_CrowdSignal_OnePrice_lemma_3_iii
-- name    : CrowdSignal.OnePrice.lemma_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:14.717445+00:00
-- url     : https://prove2.me/theorems/9118b68f-3327-4b35-bf9c-f9d7c30da232
-- title:
--   Lemma 3(iii): ordering of the indifference thresholds
-- statement:
--   Under the standing restrictions and $T\le\bar p_1$, the high type's profit when believed high at the lower barred price strictly exceeds its maximum profit under a low belief:
--   $$\pi^{HL*}<\pi^H(\bar p_1).$$
--   Moreover, any upper low-type mimicking-indifference price $\bar p'_1$ above $(3+\alpha)q_L/8$ lies strictly above every upper high-type indifference price $\underline p'_1$ above $p^{HL*}_1$, with both upper prices at most $q_H$.
--
--   These inequalities establish a nonempty range of high-type prices that deter low-type imitation while protecting the high type against a low-belief deviation.
--
--   **Formalization Note** The first inequality represents $\bar p_1>\underline p_1$ without assuming that the lower high-type crossing is feasible; it can lie below $T$. The second clause represents $\bar p'_1>\underline p'_1$.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 18, Lemma 3(iii)

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CrowdSignal.OnePrice

/-- Lemma 3(iii): ordering of the indifference thresholds. -/
theorem lemma_3_iii (P : Params) (hP : P.Standing) (hT : P.T ≤ pbar P) :
    optProfit P P.qH P.qL < profit P P.qH P.qH (pbar P) ∧
    (∀ pbar' punder' : ℝ,
      (3 + P.α) / 8 * P.qL < pbar' → pbar' ≤ P.qH →
      profit P P.qL P.qH pbar' = optProfit P P.qL P.qL →
      max ((4 * P.qL - (1 - P.α) * P.qH) / 8) P.T < punder' →
      punder' ≤ P.qH →
      profit P P.qH P.qH punder' = optProfit P P.qH P.qL →
      punder' < pbar') := by sorry

end CrowdSignal.OnePrice
