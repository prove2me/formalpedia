-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_7
-- name    : CarlssonPartition.Approx.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:31:26.98619+00:00
-- url     : https://prove2.me/theorems/e22988bd-b0f9-4df9-b2d3-65f6ba914ad3
-- title:
--   Theorem 7, p. 14 (corrected: q ≥ 2) — heavy-traffic lower bound γ²/9 for every spatially unbiased policy
-- statement:
--   Let service be heterogeneous and independent across the region: an order at $x$ has on-site time $S(x)$ with mean $\bar s(x)$ and variance $\sigma_s^2(x)$, finite at every $x\in R$, and $\iint_R\bar s(x)f(x)\,dx<\infty$. Write $\rho=\lambda\iint_R\bar s(x)f(x)\,dx/m$ and $W(\lambda)=\rho+2\lambda\iint_R\|x-x_0\|f(x)\,dx/(mvq)$. There is an absolute constant $\gamma\ge 2/(3\sqrt\pi)$ such that for every instance with capacity $q\ge2$, every stationary renewal arrival family of intensity $\lambda$, and every family $\pi_\lambda$ of admissible spatially unbiased policies,
--   $$
--   T(\pi_\lambda)\ \ge\ \frac{\gamma^2}{9}\,\frac{\lambda(1+\frac1q)^2\big[\iint_R\sqrt{f(x)}\,dx\big]^2}{m^2v^2\,(1-W(\lambda))^2}
--   \qquad\text{as } W(\lambda)\to1^- ,
--   $$
--   in the sense that for every $c<1$ the inequality with an extra factor $c$ on the right holds for all rates close enough to heavy traffic.
--
--   **Formalization Note** "As $W\to1$" is read as a liminf of the ratio. The constant $\gamma$ is existential and placed before all instances; since the bound is monotone in $\gamma$, this is equivalent to the bound with $\gamma=2/(3\sqrt\pi)$. Policies are needed only at stable rates and only eventually in heavy traffic. Costs are extended Palm expectations of actual tours (an unstable policy has cost $\infty$ and satisfies the bound).
--
--   Differences from the source:
--   - correction: The bound is stated for every positive integer capacity q. → Capacity q ≥ 2.; reason: At q = 1 tours carry one order and have no local travel, so the Lemma 3 step of the proof (p. ec8) fails; theorem_7_capacity_one_counterexample (DISPROOF.md) gives a spatially unbiased policy with T(1−W)^2 → 0. Excluded case: q = 1.
--   - correction: Only pointwise finite mean and variance of S(x). → Adds ∬_R s̄(x) f(x) dx < ∞ (FiniteMean).; reason: The source's ρ = λ∬ s̄ f/m must be finite for the workload factor to take values in (0,1) (p. 7, p. 13); otherwise no rate is stable and the statement is empty. Excluded case: infinite spatial mean service, where heavy traffic does not exist.
--   - encoding: T ≥ expression as the workload factor tends to 1, within the class of spatially unbiased policies. → For every family of policies that are eventually admissible and spatially unbiased (Definition 1, exact), for every c < 1, eventually ofReal(c·expression) ≤ T, along the stable workload-from-below filter.; reason: Liminf reading of an asymptotic lower bound; extended costs keep infinite delays.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 14 (PDF 15), Theorem 7; heterogeneous model p. 13 (PDF 14); proof p. ec8 (PDF 45)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Model
import Definitions.Def_CarlssonPartition_Approx_Supplement_AdmissiblePolicies

noncomputable section

open Filter Topology MeasureTheory
open scoped ENNReal

namespace CarlssonPartition.Approx.Supplement

/-- Theorem 7 (p. 14), corrected to capacity `q ≥ 2`: with heterogeneous independent service,
there is one absolute constant `γ ≥ 2/(3√π)` such that every family of admissible spatially
unbiased policies satisfies, in heavy traffic,
`T ≥ (γ²/9) λ (1 + 1/q)² [∬_R √f]² / (m² v² (1 - ρ - 2λ∬_R‖x - x0‖f/(mvq))²)`,
read as: for every `c < 1`, eventually `T ≥ c ·` (right-hand side). The arrival input is any
stationary renewal family of the source model. `FiniteMean` (`∬ s̄ f < ∞`) is needed for the
real workload; without it no rate is stable. At `q = 1` the printed bound is false
(`theorem_7_capacity_one_counterexample`). -/
theorem theorem_7 :
    ∃ gamma : ℝ, 2 / (3 * Real.sqrt Real.pi) ≤ gamma ∧
    ∀ (M : Model), M.Standing → 2 ≤ M.spatial.q → M.FiniteMean →
    ∀ (Ω : Type) [MeasurableSpace Ω] (A : M.InputFamily Ω)
      (U : Type) [MeasurableSpace U]
      (π : ∀ lam : M.StableRate,
        PolicyRealization (A.input ⟨lam.val, lam.property.1⟩).renewal U M.spatial.m),
      (∀ᶠ lam in M.stableHeavy,
        (π lam).Admissible M.spatial.x0 M.spatial.v M.spatial.q ∧
        (π lam).SpatiallyUnbiased M.spatial.R) →
      ∀ c : ℝ, c < 1 → ∀ᶠ lam in M.stableHeavy,
        ENNReal.ofReal (c * finiteLowerLeading M.spatial M.service gamma M.spatial.m
          lam.val M.spatial.R M.spatial.f) ≤ (π lam).cost := by sorry

end CarlssonPartition.Approx.Supplement
