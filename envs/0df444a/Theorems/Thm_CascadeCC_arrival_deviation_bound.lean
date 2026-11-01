-- Prove2me | Theorems.Thm_CascadeCC_arrival_deviation_bound
-- name    : CascadeCC.arrival_deviation_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:41.283289+00:00
-- url     : https://prove2.me/theorems/4a77ab20-5bcf-4664-870b-f2457a73399c
-- title:
--   p.ec10 — $\delta^\sigma$ is linear in $\delta^v$ and $\|\delta^\sigma\|_\infty\le Q\|\delta^v\|_\infty$
-- statement:
--   Let $a$ and $\delta$ be real vectors, and let $\hat\sigma$ be the arrival rates computed from $\hat v=v(a)-\delta$. The deviations $\delta^\sigma_j=\hat\sigma_j-\sigma_j(a)$ satisfy $\delta^\sigma_1=0$,
--
--   $$
--   \delta^\sigma_{j+1}=\zeta_j\bigl(\delta^\sigma_j+\delta_j\bigr),
--   $$
--
--   and $|\delta^\sigma_j|\le Q\|\delta\|_\infty$ for all $j$.
--
--   This is the form of $\delta^\sigma_{t,2:J}=-A^{-1}M^{-1}\delta^v_{t,1:J-1}$ used to transfer bounds on the correction to the arrival rates.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - encoding: Q = ‖−A⁻¹M⁻¹‖_∞ and the matrix form of δ^σ → Q = max_j ∑_{i<j} ∏_{i≤m<j} ζ_m and the row recursion; reason: the explicit inverse of (15), p.24, gives the same numbers
--   - generalization: δ^v_t, the policy's correction, at a^D → every real vector δ and every a; reason: the page's quantities are the case δ = δ^v_t, a = a^D
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, p.ec10 (Q); p.25 (δ^σ below (17))

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- p.ec10 and p.25 (SSRN abstract_id=3362921): the correction to σ is linear in the correction to v,
δ^σ_{2:J} = −A⁻¹M⁻¹ δ^v_{1:J−1}, in the row form δ^σ_1 = 0, δ^σ_{j+1} = ζ_j(δ^σ_j + δ^v_j), and
|δ^σ_j| ≤ Q ‖δ^v‖_∞.

**Formalization Note** The statement holds for every real vector δ and every a; the linear form replaces
the printed matrices. -/
theorem arrival_deviation_bound (M : Instance J) (a δ : Fin J → ℝ) :
    (∀ j : Fin J, j.1 = 0 → arrivalDev M a δ j = 0) ∧
      (∀ j j' : Fin J, j'.1 = j.1 + 1 →
        arrivalDev M a δ j' = M.zeta j * (arrivalDev M a δ j + δ j)) ∧
      ∀ j, |arrivalDev M a δ j| ≤ Q M * ‖δ‖ := by sorry

end CascadeCC
