-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_4_clustered_renewal_counterexample
-- name    : CarlssonPartition.Approx.Supplement.theorem_4_clustered_renewal_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:29:32.090254+00:00
-- url     : https://prove2.me/theorems/804f0d16-6e55-4a78-8e0a-505618573652
-- title:
--   Theorem 4, p. 10 (corrected: refutation for general renewal arrivals) — clustered gaps keep a dedicated-versus-flexible gap in light traffic
-- statement:
--   Theorem 4 fails for the unrestricted stationary-renewal arrival families stated in the source. Take two unit-speed capacity-one vehicles, deterministic unit on-site service, and a compact convex planar region within distance $1/100$ of its depot, with its normalized Lipschitz demand density. There exist an input family of intensity $\lambda$ and a partition into TWO districts of demand probability $1/2$ each. For $0<\lambda<1/4$ its iid renewal gaps have law
--   $$
--   G_\lambda=\tfrac12\delta_{1/4}+\tfrac12\delta_{2/\lambda-1/4}.
--   $$
--   Eventually as $\lambda\to0^+$ an actual causal flexible policy and every physically valid stationary dedicated execution satisfy
--   $$
--   T(\pi_\lambda)\le\frac65<\frac54\le T(E).
--   $$
--   The persistent gap is at least $1/20$. Both bounds, the input family, partition and flexible policy witnesses are conclusions. No desired performance or queueing expectation is assumed. A uniform disk supplies a nondegenerate source instance. Every district is nonempty and has positive demand, so the refutation uses no empty- or null-district convention.
--
--   **Formalization Note** Rates use a cofinal positive neighborhood of zero with a proved nontrivial light-traffic filter; the input family is defined at all positive rates. Costs are extended Palm expectations of actual depot tours. The dedicated bound even covers anticipative physical executions, while the upper witness is causal. Service is strictly positive. DISPROOF.md checks the geometric-cluster lower bound and alternating-driver upper witness by hand; the Lean theorem is an open statement stub. The corrected positive statement under Poisson arrivals is the separate item `theorem_4`.
--
--   Differences from the source:
--   - correction: Every spatial partition is optimal as the stationary renewal arrival intensity tends to zero. → For two vehicles, capacity one, speed one and homogeneous unit service in a region of radius at most 1/100, there exists a stationary renewal family and a partition for which every physical dedicated execution costs at least 5/4 while an actual causal flexible policy eventually costs at most 6/5.; reason: PDF 7–8 allows general renewal laws and specifies no cross-rate scaling convention. The family with gaps 1/4 and 2/λ−1/4, each with probability 1/2, retains short bursts at vanishing intensity; the ec4 M/G/1 argument does not apply. DISPROOF.md gives the geometric-cluster lower bound and alternating-driver upper construction.
--   - encoding: The theorem concerns actual expected delivery time in light traffic for an arbitrary dedicated partition. → Expectations are extended Palm integrals over actual depot tours; a cofinal subtype of rates carries a proved nontrivial λ→0+ filter. Each of two districts has demand mass 1/2; neither is empty or null. The lower bound quantifies over all valid stationary dedicated executions, even anticipative ones; the upper witness is causal with independent randomization.; reason: Infinite delays cannot default to zero. The stronger lower comparison avoids assuming a source-optimum formula or identifying the causal-interface prototype with the whole admissible policy class. A uniform demand density on a small disk witnesses the spatial premises; no degenerate region is needed.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 10 (PDF 11), Theorem 4; renewal domain pp. 6–7 (PDF 7–8); proof pp. ec3–ec4 (PDF 40–41)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_LightTraffic

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory Filter
open scoped ENNReal

/-- Theorem 4's full renewal-domain claim fails without a condition controlling the
arrival-law family as λ→0. The counterexample keeps ordinary homogeneous unit service,
positive speed, two vehicles, capacity one and a nondegenerate compact planar region.
Both districts have demand probability one half, avoiding empty or null districts.
The lower bound applies even to physically valid anticipative dedicated executions;
the upper witness must be an actual causal, stationary flexible routing realization.
Neither performance bound is a premise. -/
theorem theorem_4_clustered_renewal_counterexample
    (M : Model) (hStanding : M.Standing)
    (hm : M.spatial.m = 2) (hv : M.spatial.v = 1) (hq : M.spatial.q = 1)
    (hs : M.spatial.sbar = 1)
    (hsmall : M.spatial.R ⊆ Metric.closedBall M.spatial.x0 (1 / 100 : ℝ))
    (hservice : ∀ x ∈ M.spatial.R, M.service.law x = Measure.dirac (1 : ℝ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (A : M.InputFamily Ω)
      (Rs : Fin M.spatial.m → Set CarlssonPartition.Equitable.Plane),
      M.spatial.IsPartition Rs ∧
      (∀ i, M.spatial.pr (Rs i) = (1 / 2 : ℝ)) ∧
      (∀ lam : LightRate, (A.atLight lam).renewal.gapLaw = clusteredGapLaw lam.val) ∧
      ∀ᶠ lam : LightRate in lightTraffic,
        (∃ π : PolicyRealization (A.atLight lam).renewal ℝ M.spatial.m,
          π.Admissible M.spatial.x0 M.spatial.v M.spatial.q ∧
          π.cost ≤ (6 / 5 : ℝ≥0∞)) ∧
        (∀ E : Execution (A.atLight lam).renewal M.spatial.m,
          E.Valid M.spatial.x0 M.spatial.v M.spatial.q →
          E.StationaryCosts → E.DedicatedTo Rs →
          (5 / 4 : ℝ≥0∞) ≤ E.meanDelivery) := by sorry

end CarlssonPartition.Approx.Supplement
