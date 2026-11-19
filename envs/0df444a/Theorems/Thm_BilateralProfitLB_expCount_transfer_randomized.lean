-- Prove2me | Theorems.Thm_BilateralProfitLB_expCount_transfer_randomized
-- name    : BilateralProfitLB.expCount_transfer_randomized
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-18T13:20:42.123858+00:00
-- url     : https://prove2.me/theorems/0cb75c77-75bc-4368-bb39-b83c5fa53d8d
-- title:
--   Expected visit comparison for randomized two-bit policies
-- statement:
--   Fix an integer $K\ge 1$, a perturbation index $1\le j\le K$, and a horizon $T\ge 0$. Consider a posted-price policy that draws a random seed with a probability law and observes the separate seller and buyer acceptance bits after each round. The seed is independent of all valuations. The policy posts a pair in $[0,1]^2$ as a measurable function of the seed for each fixed history of acceptance bits.
--
--   Let $N_j$ count the rounds in which the posted buyer price lies in the perturbation interval $I_j$. Write $\mathbb E^j$ and $\mathbb E^0$ for the expectations under the $j$-th perturbed law and the baseline law, respectively. Each expectation is over the policy seed and the $T$ independent valuation pairs drawn from the indicated law. Then
--   $$
--   \mathbb E^j[N_j]-\mathbb E^0[N_j]
--   \le \frac{T}{22K^2}\sqrt{\mathbb E^0[N_j]}.
--   $$
--
--   **Formalization Note.** Claim 3.6 states this inequality for deterministic policies. The extension here retains the independent seed in the transcript and uses the same seed law under both instances. It holds on any measurable seed space with a probability measure. The intervals, price bounds, and inclusive acceptance events are those of Section 7.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Section 7, pp.49–52 (PDF 51–54), randomized-policy extension of Claim 3.6, pp.51–52 (PDF 53–54).

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic

open MeasureTheory BilateralProfitLB

theorem BilateralProfitLB.expCount_transfer_randomized (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (T : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (π : Policy Ω) :
    expCount π P (law K j) T (I K j) - expCount π P (law K 0) T (I K j) ≤
      (T : ℝ) / (22 * (K : ℝ) ^ 2) * Real.sqrt (expCount π P (law K 0) T (I K j)) := by sorry
