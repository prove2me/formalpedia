-- Prove2me | Theorems.Thm_DynStochMatching_Reward_claim_5
-- name    : DynStochMatching.Reward.claim_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:43:35.969292+00:00
-- url     : https://prove2.me/theorems/f12e208f-f02a-481e-8ee1-7c39056939c4
-- title:
--   Claim 5 — Nested compatibility flow decomposition
-- statement:
--   Fix an ordinary or bipartite-asymmetric instance and any QB-feasible flow satisfying all applicable B.3 performance bounds. For a type i, sort its positive outgoing support as σ_i and form the nested compatibility sets and backward weights by (24)–(25). Every weight is nonnegative; each outgoing edge flow equals its displayed sum of component contributions, and abandonment flow equals the displayed sum of abandonment contributions. No saturation assumption is added, including when the support is empty. The abandonment identity is retained as printed despite finding I2.
--
--   Source statement:
--
--   For every $\ell\in[1,|S_i|]$, we have $\hat\lambda_{i,\ell}\ge0$ and $\tilde x_{i,\sigma_i(\ell)}=\sum_{q=\ell}^{|S_i|}\frac{\lambda^p_{\sigma_i(\ell)}}{\mu_i+\sum_{j\in S_i^q}\lambda^p_j}\cdot\hat\lambda_{i,q}$. Furthermore, we have $\tilde x_{i,a}=\sum_{\ell=1}^{|S_i|}\frac{\mu_i}{\mu_i+\sum_{j\in S_i^\ell}\lambda^p_j}\cdot\hat\lambda_{i,\ell}$.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - encoding: independently marked Poisson arrivals and randomized adapted policies → a canonical product of independent exponential seeds, inverse CDF marks and pair stopping times up to null events; reason: this realizes the same laws and observable information; null modifications remove impossible seed paths without revealing future arrivals or sojourns
--   - encoding: the optimal online policy value r* or c* → supremum or infimum over all feasible observable policies in complete extended orders; reason: no optimum is supplied as an input; explicit attainment clauses retain the source optimum convention where used
--   - encoding: compatibility indices 1 through the support size → zero-based indices with prefix length l+1; reason: the endpoints and all terms of every source sum are preserved
--   - encoding: infinite abandonment-rate shorthand on the immediate side → a separate immediate lifetime constructor and zero outgoing active flow; reason: immediate vertices are available for their arrival decision and no infinite real product is evaluated
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Claim 5, printed p. 43 / PDF p. 44

import Definitions.Def_DynStochMatching_Reward_Algorithm

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem claim_5 {n : ℕ} (D : Instance n) (x : Flow n)
    (hsource : sourceDomain D) (hfeasible : qbFeasible D x) (hperformance : flowGuarantees D x)
    (i : Fin n) :
    (∀ l : Fin (support x i).length,
      0 ≤ decomposition D x i l.val ∧
      x.edge i ((support x i)[l.val]) =
        ∑ q ∈ Finset.Ico l.val (support x i).length,
          passiveRate x ((support x i)[l.val]) / decompositionDenominator D x i q *
            decomposition D x i q) ∧
    x.abandon i = ∑ l ∈ Finset.range (support x i).length,
      finiteDeathRate (D.lifetime i) / decompositionDenominator D x i l * decomposition D x i l := by sorry

end DynStochMatching.Reward
