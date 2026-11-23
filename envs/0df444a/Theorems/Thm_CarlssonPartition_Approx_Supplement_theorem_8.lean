-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_8
-- name    : CarlssonPartition.Approx.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:33:44.575162+00:00
-- url     : https://prove2.me/theorems/d24cfa4f-cf58-41be-9e36-3a704066f7fc
-- title:
--   Theorem 8, p. 14 (corrected: q ≥ 2, Poisson, finite spatial second moment) — a spatially unbiased policy attains the β²/2 leading term
-- statement:
--   Let service be heterogeneous and independent across the region as in §3.4, with capacity $q\ge2$, arrivals forming a stationary Poisson process of intensity $\lambda$, and a finite spatial second moment $E[S(X)^2]=\iint_R E[S(x)^2]f(x)\,dx<\infty$. With $\rho=\lambda\iint_R\bar s(x)f(x)\,dx/m$ and $W(\lambda)=\rho+2\lambda\iint_R\|x-x_0\|f(x)\,dx/(mvq)$, there are policies $\tilde\pi^*_\lambda$, admissible, spatially unbiased (Definition 1) and of finite expected delivery time in heavy traffic, such that
--   $$
--   T(\tilde\pi^*_\lambda)\ \sim\ \frac{\beta^2\lambda(1-\frac1q)^2\big[\iint_R\sqrt{f(x)}\,dx\big]^2}{2m^2v^2(1-W(\lambda))^2}\qquad\text{as }W(\lambda)\to1^- .
--   $$
--
--   **Formalization Note** "$\sim$" is a ratio tending to $1$ along the workload-from-below filter on stable rates. Policies are existential and may depend on $\lambda$ (the proof tunes its batch size). Three hypotheses are added, each excluding a case where the printed claim fails; see the list below.
--
--   Differences from the source:
--   - correction: Every positive integer capacity q. → Capacity q ≥ 2.; reason: At q = 1 the factor (1−1/q)^2 makes the leading term identically zero, so no delivery time is asymptotic to it (theorem_8_capacity_one_counterexample); the proof (p. ec11) divides by 1−1/q. Excluded case: q = 1.
--   - correction: Only pointwise finite mean and variance of S(x) (p. 13). → Adds a finite spatial second moment of service.; reason: With one vehicle and E[S(X)^2] = ∞ (e.g. S(x) = 1 + x_1^{-3/4} on the unit square), every policy has infinite expected delay by a residual-service argument (DISPROOF.md); the proof (p. ec10) uses spatially averaged variances, which presuppose this. Excluded case: infinite spatial second moment.
--   - correction: Arrivals are a stationary renewal process of intensity λ, with no convention for how its law varies with λ. → Poisson arrivals at every rate.; reason: For renewal families whose gap variance grows fast enough with λ, the queueing delay exceeds the leading term. The proof's queueing formula (p. ec11) uses the interarrival variance 1/λ², the Poisson value, and Theorem 3 (Bertsimas and van Ryzin 1993b) is stated for Poisson arrivals. Excluded cases: non-exponential renewal inputs.
--   - encoding: There exists a provably good spatially unbiased policy with T ∼ expression as the workload factor tends to 1. → There exist a seed space and policies indexed by stable rates, eventually admissible, spatially unbiased and of finite cost in heavy traffic, with cost.toReal / expression → 1 along the stable workload-from-below filter.; reason: Ratio convention of the series for ∼; finiteness is a conclusion, so toReal is meaningful.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 14 (PDF 15), Theorem 8; heterogeneous model p. 13 (PDF 14); proof pp. ec9–ec11 (PDF 46–48)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Model
import Definitions.Def_CarlssonPartition_Approx_Supplement_AdmissiblePolicies

noncomputable section

open Filter Topology MeasureTheory
open scoped ENNReal

namespace CarlssonPartition.Approx.Supplement

/-- Theorem 8 (p. 14), corrected to capacity `q ≥ 2`, Poisson arrivals and a finite spatial
second moment of service: with heterogeneous independent service there are admissible,
spatially unbiased policies `π̃*` (one for each stable rate, required in heavy traffic) of finite expected delivery time
with `T(π̃*) ∼ β² λ (1 - 1/q)² [∬_R √f]² / (2 m² v² (1 - ρ - 2λ∬_R‖x - x0‖f/(mvq))²)`,
`ρ = λ ∬_R s̄(x) f / m`, as the workload factor tends to `1` from below.
Each added hypothesis excludes a case where the printed claim is false: `q = 1` (the leading
term vanishes, `theorem_8_capacity_one_counterexample`); an infinite spatial second moment
(one vehicle then has infinite expected delay under every policy, DISPROOF.md); and renewal
families whose gap law degenerates with `λ` (burstiness adds delay beyond the leading term).
The interarrival variance `1/λ²` of the proof (p. ec11) is the Poisson one. -/
theorem theorem_8 (M : Model) (hStanding : M.Standing) (hq : 2 ≤ M.spatial.q)
    (hsecond : M.service.spatialSecond (locationLaw M.spatial) < ⊤)
    (Ω : Type) [MeasurableSpace Ω] (A : M.InputFamily Ω) (hA : A.Poisson) :
    ∃ (U : Type) (_ : MeasurableSpace U)
      (π : ∀ lam : M.StableRate,
        PolicyRealization (A.input ⟨lam.val, lam.property.1⟩).renewal U M.spatial.m),
      (∀ᶠ lam in M.stableHeavy, (π lam).Admissible M.spatial.x0 M.spatial.v M.spatial.q ∧
        (π lam).SpatiallyUnbiased M.spatial.R ∧ (π lam).cost < ⊤) ∧
      Tendsto (fun lam : M.StableRate => (π lam).cost.toReal /
          finiteLeading M.spatial M.service M.spatial.m lam.val M.spatial.R M.spatial.f)
        M.stableHeavy (𝓝 1) := by sorry

end CarlssonPartition.Approx.Supplement
