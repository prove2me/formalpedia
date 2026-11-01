-- Prove2me | Theorems.Thm_CascadeCC_lemma_EC1_joint_concavity
-- name    : CascadeCC.lemma_EC1_joint_concavity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:24.445908+00:00
-- url     : https://prove2.me/theorems/3a326b2f-225a-4355-90a4-05979c8fd8a5
-- title:
--   Lemma EC.1 — $R^D$ is jointly concave in $(\sigma_j,z)$
-- statement:
--   Let $R^D_j(\sigma,z)$ be the deterministic revenue-to-go from product $j$ over $n$ periods, with arrival rates $\sigma$ and inventories $z$. For every $n$ and $j$, the map
--
--   $$
--   (\sigma,z)\longmapsto R^D_j(\sigma,z)
--   $$
--
--   is concave on $\{(\sigma,z):\sigma\ge0,\ z\ge0\}$.
--
--   This is the structural fact behind the stationarity of DET: DET is not concave in the rates, but its value is concave in the arrival rates and inventories.
--
--   **Formalization Note** `Rev` is a supremum, so no attainment is used. The printed proof takes optimal solutions of (EC.20a).
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - encoding: max in (EC.20a), with periods t, …, T → a supremum over n = T − t + 1 periods, on the domain σ, z ≥ 0; reason: stage maximizers need not exist; the supremum is the max when it is attained, and σ, z ≥ 0 is the set the recursion stays in
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, Lemma EC.1, p.ec5

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- Lemma EC.1, p.ec5 (SSRN abstract_id=3362921): R^D_tj(σ_j, z) is jointly concave in (σ_j, z).

**Formalization Note** The domain is σ, z ≥ 0, the set the recursion stays in, and `n` is the number of
remaining periods. `Rev` is a supremum, so no optimal solution is assumed. -/
theorem lemma_EC1_joint_concavity (M : Instance J) (n j : ℕ) :
    ConcaveOn ℝ {p : (Fin n → ℝ) × (Fin J → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2}
      (fun p => Rev M n j p.1 p.2) := by sorry

end CascadeCC
