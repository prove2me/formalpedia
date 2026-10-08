-- Prove2me | Theorems.Thm_ChenBullwhip_Centralized_theorem_3_1
-- name    : ChenBullwhip.Centralized.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:55:39.651313+00:00
-- url     : https://prove2.me/theorems/fb8bd400-67ab-4319-b22c-c10434355c72
-- title:
--   Theorem 3.1 — with centralized demand information, $\mathrm{Var}(q^k)/\mathrm{Var}(D) \ge 1 + (2S_k/p + 2S_k^2/p^2)(1-\rho^p)$, $S_k = \sum_{i\le k} L_i$
-- statement:
--   **Theorem 3.1.** Consider a multistage supply chain in which the retailer (stage $1$) shares all customer demand information with every stage. The demands are the steady-state AR(1) process $D_t = \mu + \rho D_{t-1} + \epsilon_t$ with $|\rho| < 1$ and errors $\epsilon_t$ i.i.d. from a symmetric distribution with mean $0$ and variance $\sigma^2 > 0$. Every stage uses the moving average $\hat D_t = \sum_{i=1}^p D_{t-i}/p$ with the same $p \ge 1$, and stage $k$ follows the order-up-to policy $y^k_t = L_k\hat D_t + z_k\hat\sigma^{L_k}_{et}$, where $L_k$ is the lead time between stages $k$ and $k+1$, $z_k$ is a constant and $\hat\sigma^{L_k}_{et} = C_{L_k,\rho}\sqrt{\sum_{i=1}^p (e_{t-i})^2/p}$. Let $q^k_t$ be the order placed by stage $k$ in period $t$ (stage $1$: $q^1_t = y^1_t - y^1_{t-1} + D_{t-1}$; stage $k \ge 2$: $q^k_t = y^k_t - y^k_{t-1} + q^{k-1}_t$). Then for every stage $k \ge 1$ and every period $t$,
--
--   $$\frac{\mathrm{Var}(q^k_t)}{\mathrm{Var}(D_t)} \ge 1 + \left(\frac{2\sum_{i=1}^k L_i}{p} + \frac{2\left(\sum_{i=1}^k L_i\right)^2}{p^2}\right)(1-\rho^p),$$
--
--   and the bound is tight when $z_i = 0$ for $i = 1, \dots, k$: then the ratio equals the right-hand side.
--
--   The bound grows with the total lead time $\sum_{i\le k} L_i$ upstream of stage $k$, so even when demand information is fully centralized and every stage uses the same forecast and the same policy, the variability of orders increases along the chain: centralizing demand information does not eliminate the bullwhip effect. For $k = 1$ the theorem is Theorem 2.2.
--
--   **Formalization Note** "Tight when $z_i = 0$" is formalized as equality under that hypothesis. The paper gives no formula for $q^k_t$; the recursion above is read from its sequence of events (see the definition of the chain). The unspecified constants $C_{L_k,\rho}$ are $C(L_k)$ for an arbitrary real function $C$; the bound does not depend on them. Stages are numbered from $1$, and $\sigma > 0$ is a field of the demand structure.
-- source:
--   Chen, Drezner, Ryan and Simchi-Levi, Quantifying the Bullwhip Effect in a Simple Supply Chain, Management Science 46 (2000), p. 441, Theorem 3.1

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy
import Definitions.Def_ChenBullwhip_Centralized_Chain

namespace ChenBullwhip.Centralized

theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (p : ℕ) (hp : 1 ≤ p)
    (L : ℕ → ℕ) (C z : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (t : ℤ) :
    ProbabilityTheory.variance (X.chainOrder p L C z k t) P
          / ProbabilityTheory.variance (X.D t) P
        ≥ 1 + (2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) / p
              + 2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2) * (1 - X.rho ^ p)
      ∧ ((∀ i ∈ Finset.Icc 1 k, z i = 0) →
          ProbabilityTheory.variance (X.chainOrder p L C z k t) P
              / ProbabilityTheory.variance (X.D t) P
            = 1 + (2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) / p
              + 2 * ((∑ i ∈ Finset.Icc 1 k, L i : ℕ) : ℝ) ^ 2 / (p : ℝ) ^ 2)
                * (1 - X.rho ^ p)) := by sorry

end ChenBullwhip.Centralized
