-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_7_capacity_one_counterexample
-- name    : CarlssonPartition.Approx.Supplement.theorem_7_capacity_one_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:32:24.373666+00:00
-- url     : https://prove2.me/theorems/1e874526-1abf-4db6-8e27-0f5a013e2f7b
-- title:
--   Theorem 7, p. 14 (corrected: refutation at capacity q = 1) — a spatially unbiased policy with T(1−W)² → 0
-- statement:
--   Theorem 7's printed lower bound fails at the allowed capacity $q=1$. Take one vehicle of unit speed on a compact convex planar region contained in the unit ball about the depot, with the source's normalized Lipschitz demand density. Give location $x$ the deterministic service duration $1+\|x-x_0\|$, a bounded, location-dependent independent service law with finite pointwise moments. There exist a stationary renewal input family and, at every positive stable rate, actual causal spatially unbiased routing policies of finite expected delivery time such that
--   $$
--   T(\pi_\lambda)\,(1-W(\lambda))^2\longrightarrow0
--   \quad\text{as }W(\lambda)\to1^-.
--   $$
--   The stable heavy-traffic filter is explicitly nontrivial. Since the printed coefficient $\gamma^2\lambda(1+1/q)^2[\iint_R\sqrt f]^2/(9m^2v^2)$ tends to a strictly positive value, this contradicts every allowed positive $\gamma$, including $2/(3\sqrt\pi)$. No desired performance or unbiasedness property is a premise. The input and all policy witnesses are conclusions.
--
--   **Formalization Note** This refutes the printed claim at $q=1$. The corrected positive statement for $q\ge2$ is the separate item `theorem_7`. The hand construction uses Poisson arrivals, eligibility delay $1-\|x-x_0\|$ and one-order FCFS depot trips. Expected costs are computed from actual tours and integrated under Palm probability. A uniform disk and density supply a nondegenerate source instance.
--
--   Differences from the source:
--   - correction: Every spatially unbiased policy satisfies the gamma-squared quadratic heavy-traffic lower bound for every positive integer capacity. → At capacity one, one vehicle and unit speed, a bounded genuinely location-dependent service field admits a causal spatially unbiased policy with T(1-W)^2 tending to zero on a nontrivial stable heavy-traffic filter.; reason: Poisson arrivals are allowed renewal arrivals. Location-dependent eligibility delay 1-r followed by one-order FCFS makes waiting equal to 1 plus an M/G/1 workload independent of the current location. Busy time is 1+3r, bounded by 4. Expected delay grows only as 1/(1-W). The printed coefficient is strictly positive. DISPROOF.md gives the complete hand counterexample; the corrected q>=2 lower bound is the separate item theorem_7.
--   - encoding: Actual dispatching policies and their expected waiting and delivery times in the source routing model. → Existential marked renewal input family and causal physical routing realizations; costs are extended Palm expectations. StableRate contains only positive rates with workload below one. Nontriviality of stableHeavy is a conclusion.; reason: The witness uses actual tours and costs. Requiring admissible policies at all positive rates, including overload, would vacuate the former lower-bound statement. Unit-or-longer services avoid the unresolved zero-service event-ordering boundary.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 14 (PDF 15), Theorem 7; heterogeneous model p. 13 (PDF 14); proof p. ec8 (PDF 45)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Model
import Definitions.Def_CarlssonPartition_Approx_Supplement_AdmissiblePolicies

noncomputable section

open Filter Topology MeasureTheory
open scoped ENNReal

namespace CarlssonPartition.Approx.Supplement

/-- Counterexample to Theorem 7 on its allowed capacity-one domain. Choose one vehicle,
unit speed, and the bounded, location-dependent deterministic service duration
`1 + ‖x - x0‖` on a region of radius at most one. A stationary Poisson input admits a
causal spatially unbiased one-order-trip policy with delivery time of order `1/(1-W)`.
Consequently its actual expected delivery time times `(1-W)^2` tends to zero, contradicting
EVERY positive coefficient of the printed quadratic lower bound. No performance or
unbiasedness property is assumed; the input and all policy witnesses are conclusions.
The stable-rate domain avoids demanding a stationary policy in overload. -/
theorem theorem_7_capacity_one_counterexample
    (M : Model) (hStanding : M.Standing)
    (hm : M.spatial.m = 1) (hv : M.spatial.v = 1) (hq : M.spatial.q = 1)
    (hsmall : M.spatial.R ⊆ Metric.closedBall M.spatial.x0 (1 : ℝ))
    (hservice : ∀ x ∈ M.spatial.R,
      M.service.law x = Measure.dirac (1 + ‖x - M.spatial.x0‖)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (A : M.InputFamily Ω)
      (π : ∀ lam : M.StableRate,
        PolicyRealization (A.input ⟨lam.val, lam.property.1⟩).renewal ℝ M.spatial.m),
      NeBot M.stableHeavy ∧
      (∀ lam, (π lam).Admissible M.spatial.x0 M.spatial.v M.spatial.q ∧
        (π lam).SpatiallyUnbiased M.spatial.R ∧ (π lam).cost < ⊤) ∧
      Tendsto (fun lam : M.StableRate =>
        (π lam).cost * ENNReal.ofReal
          ((1 - finiteWorkload M.spatial M.service M.spatial.m lam.val
            M.spatial.R M.spatial.f) ^ 2))
        M.stableHeavy (𝓝 0) := by sorry

end CarlssonPartition.Approx.Supplement
