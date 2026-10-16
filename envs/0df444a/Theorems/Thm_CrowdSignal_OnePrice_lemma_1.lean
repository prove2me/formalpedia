-- Prove2me | Theorems.Thm_CrowdSignal_OnePrice_lemma_1
-- name    : CrowdSignal.OnePrice.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:00.502963+00:00
-- url     : https://prove2.me/theorems/c69be5b2-0c90-4052-9f1c-64de682d008a
-- title:
--   Lemma 1: optimal regular selling price and profit
-- statement:
--   Fix a parameter tuple with $0<q_L<q_H$, $0<\alpha<1$, and $T>0$. Let each of the true and believed qualities, $q_i$ and $q_j$, be either $q_L$ or $q_H$. Given $T\le p_1<q_j$, the following prices in $(0,q_i]$ attain the maximum of the conditional regular-period profit $\pi^{ij}_2(\cdot\mid p_1)$:
--   $$
--   (p^{ij*}_2,\pi^{ij*}_2)=\begin{cases}
--   (q_i/2,[\alpha/(1-p_1/q_j)+(1-\alpha)]q_i/4),&p_1<q_j/2,\\
--   (p_1q_i/q_j,\alpha p_1q_i/q_j+(1-\alpha)(1-p_1/q_j)p_1q_i/q_j),&q_j/2\le p_1<\min\{q_j/[2(1-\alpha)],q_j\},\\
--   (q_i/[2(1-\alpha)],\alpha q_i/[2(1-\alpha)]+[1-1/[2(1-\alpha)]]q_i/2),&\min\{q_j/[2(1-\alpha)],q_j\}\le p_1<q_j.
--   \end{cases}
--   $$
--   This characterizes the regular-period choice used in both the funding profit and the subsequent equilibrium analysis.
--
--   **Formalization Note** Parts (ii) and (iii) of the printed lemma restrict these same cases by the value of $T$; the three implications include those restrictions. The endpoint $p_1=q_j$ is excluded because the printed third-case price can leave the feasible price interval there when $\alpha\ge1/2$.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 14, Lemma 1, (2)–(3)

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CrowdSignal.OnePrice

/-- Lemma 1, including the three price ranges of (3). -/
theorem lemma_1 (P : Params) (hP : P.Standing) (qi qj p1 : ℝ)
    (hi : qi = P.qL ∨ qi = P.qH) (hj : qj = P.qL ∨ qj = P.qH)
    (hfund : P.T ≤ p1) (hbelow : p1 < qj) :
    (p1 < qj / 2 →
      qi / 2 ∈ Set.Ioc (0 : ℝ) qi ∧
      IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi)
        ((P.α / (1 - p1 / qj) + (1 - P.α)) * qi / 4) ∧
      rsProfit P qi qj p1 (qi / 2) =
        (P.α / (1 - p1 / qj) + (1 - P.α)) * qi / 4) ∧
    (qj / 2 ≤ p1 → p1 < min (qj / (2 * (1 - P.α))) qj →
      p1 * qi / qj ∈ Set.Ioc (0 : ℝ) qi ∧
      IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi)
        (P.α * (p1 * qi / qj) +
          (1 - P.α) * (1 - p1 / qj) * (p1 * qi / qj)) ∧
      rsProfit P qi qj p1 (p1 * qi / qj) =
        P.α * (p1 * qi / qj) +
          (1 - P.α) * (1 - p1 / qj) * (p1 * qi / qj)) ∧
    (min (qj / (2 * (1 - P.α))) qj ≤ p1 →
      qi / (2 * (1 - P.α)) ∈ Set.Ioc (0 : ℝ) qi ∧
      IsGreatest (rsProfit P qi qj p1 '' Set.Ioc (0 : ℝ) qi)
        (P.α * (qi / (2 * (1 - P.α))) +
          (1 - 1 / (2 * (1 - P.α))) * qi / 2) ∧
      rsProfit P qi qj p1 (qi / (2 * (1 - P.α))) =
        P.α * (qi / (2 * (1 - P.α))) +
          (1 - 1 / (2 * (1 - P.α))) * qi / 2) := by sorry

end CrowdSignal.OnePrice
