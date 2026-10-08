-- Prove2me | Theorems.Thm_ChenBullwhip_Decentralized_theorem_3_2
-- name    : ChenBullwhip.Decentralized.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:35:00.056335+00:00
-- url     : https://prove2.me/theorems/f863b687-e756-46ce-86dc-2eda62567579
-- title:
--   Theorem 3.2 — without shared demand information, $\mathrm{Var}(q^k)/\mathrm{Var}(D) \ge \prod_{i=1}^k (1 + 2L_i/p + 2L_i^2/p^2)$
-- statement:
--   Consider a serial supply chain in which the retailer (stage 1) faces demands $D_t = \mu + \epsilon_t$, where the errors $\epsilon_t$ are independent and identically distributed from a symmetric distribution with mean $0$ and variance $\sigma^2 > 0$. No demand information is shared: every stage $k$ forecasts from the orders it receives, with moving averages over $p \ge 1$ observations,
--
--   $$\hat D^{(1)}_t = \frac{\sum_{i=1}^p D_{t-i}}{p}, \qquad \hat D^{(k)}_t = \frac{\sum_{j=0}^{p-1} q^{k-1}_{t-j}}{p} \quad (k \ge 2),$$
--
--   and follows the order-up-to policy $y^k_t = L_k \hat D^{(k)}_t$, where $L_k \in \mathbb N$ is the lead time between stages $k$ and $k+1$. Stage $k$'s orders are $q^1_t = y^1_t - y^1_{t-1} + D_{t-1}$ and $q^k_t = y^k_t - y^k_{t-1} + q^{k-1}_t$ for $k \ge 2$. Then for every stage $k \ge 1$ and every period $t$
--
--   $$\frac{\operatorname{Var}(q^k_t)}{\operatorname{Var}(D_t)} \;\ge\; \prod_{i=1}^{k}\left(1 + \frac{2L_i}{p} + \frac{2L_i^2}{p^2}\right).$$
--
--   This is Theorem 3.2 (Eq. (7)) of Chen, Drezner, Ryan and Simchi-Levi (2000). Compared with the centralized chain, where the amplification at stage $k$ is the additive expression $1 + 2(\sum_{i\le k} L_i)/p + 2(\sum_{i\le k} L_i)^2/p^2$ (Eq. (8)), the lower bound here is multiplicative in the stages, which is the paper's quantitative case for sharing demand information.
--
--   **Formalization Note** The order recursion for $q^k_t$ is not printed in the paper; it is the §2.2 identity $q_t = y_t - y_{t-1} + D_{t-1}$ applied to stage $k$, whose incoming demand is $q^{k-1}_t$ (sequence of events, p. 440). The hypothesis $p \ge 1$ is implicit in the paper; $\sigma > 0$ and square-integrable errors make the ratio genuine. No stationarity assumption is made: the statement holds in every period $t$.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 441, Theorem 3.2, Eq. (7)

import Mathlib
import Definitions.Def_ChenBullwhip_Decentralized_IIDDemand
import Definitions.Def_ChenBullwhip_Decentralized_Chain

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Decentralized

/-- Theorem 3.2, Eq. (7): in the decentralized chain with i.i.d. symmetric demand, moving
averages over `p ≥ 1` observations and order-up-to points `y^k_t = L_k D̂^{(k)}_t`, the orders
`q^k_t` of every stage `k ≥ 1` satisfy
`Var(q^k_t)/Var(D_t) ≥ ∏_{i=1}^k (1 + 2L_i/p + 2L_i²/p²)` in every period `t`. -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : IIDDemand P) (p : ℕ) (hp : 1 ≤ p) (L : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) (t : ℤ) :
    variance (X.stageOrder p L k t) P / variance (X.D t) P
      ≥ ∏ i ∈ Finset.Icc 1 k, (1 + 2 * (L i : ℝ) / p + 2 * (L i : ℝ) ^ 2 / (p : ℝ) ^ 2) := by sorry

end ChenBullwhip.Decentralized
