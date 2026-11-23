-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_4
-- name    : CarlssonPartition.Approx.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:28:33.849205+00:00
-- url     : https://prove2.me/theorems/53632d27-328f-4d17-84ae-45d6ac32045b
-- title:
--   Theorem 4, p. 10 (corrected: Poisson arrivals) — every region partition is optimal in light traffic
-- statement:
--   Consider the source model with homogeneous iid on-site service of mean $\bar s$ (one service law at every location), $m$ vehicles of speed $v$ and capacity $q$, a compact convex region $R$ with depot $x_0\in R$ and a Lipschitz demand density $f$. Let $\{R_1,\dots,R_m\}$ be ANY partition of $R$ (pieces null-measurable, pairwise disjoint up to area zero, union $R$; empty or zero-demand districts are allowed), and let the arrivals form, at each rate $\lambda>0$, a stationary Poisson process of intensity $\lambda$ with iid location/service marks. Put
--   $$
--   T_0=\frac1v\iint_R\|x-x_0\|f(x)\,dx+\bar s .
--   $$
--   Then (i) at every rate, every admissible (causal, physically feasible, stationary) policy, flexible or dedicated, has expected delivery time $T(\pi)\ge T_0$; and (ii) there are admissible policies dedicated to the districts $R_i$ (driver $i$ serves only orders located in $R_i$) whose expected delivery times satisfy
--   $$
--   T(\pi_\lambda)\longrightarrow T_0\qquad(\lambda\to0^+).
--   $$
--   So the region partitioning policy attains, in light traffic, the optimal expected delivery time, which is the source's statement.
--
--   **Formalization Note** Costs are extended Palm expectations of actual depot tours; the light-traffic limit is along $\lambda\to0^+$. The bound (i) is the paper's (EC.1), with the speed divisor $1/v$ that the paper's ec4 computation has and (EC.1) omits. Poisson arrivals are added: the source model allows general stationary renewal arrivals, but its proof treats each district as an M/G/1 queue (p. ec4), and `theorem_4_clustered_renewal_counterexample` shows the claim is false for renewal families whose gap law keeps short bursts as $\lambda\to0$.
--
--   Differences from the source:
--   - correction: Arrivals are a stationary renewal process of intensity λ, with no convention for how its law varies as λ→0. → Arrivals are Poisson at every rate (exponential gaps of rate λ).; reason: The printed claim fails for renewal families with persistent short gaps (theorem_4_clustered_renewal_counterexample, DISPROOF.md). The source proof (p. ec4) models each district as an M/G/1 queue, i.e. Poisson arrivals; Theorem 3 (Bertsimas and van Ryzin 1993b) is also stated for Poisson arrivals. Excluded cases: non-exponential renewal inputs.
--   - correction: The light-traffic value (EC.1) is ∬_R‖x−x0‖f(x)dx + s̄. → The light-traffic value is ∬_R‖x−x0‖f(x)dx / v + s̄.; reason: Units: travel time is distance over speed; the paper's own ec4 display divides by v. No case is excluded.
--   - encoding: The region partitioning policy is optimal in light traffic: its expected delivery time equals the optimal policy's. → Every admissible policy costs at least T0 at every rate, and admissible dedicated policies have cost tending to T0 as λ→0+.; reason: This is the optimal value statement in its strongest form: the lower bound is the paper's (EC.1), the limit is its ec4 computation. Costs are extended nonnegative Palm expectations, so an infinite delay cannot default to zero.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 10 (PDF 11), Theorem 4; model p. 6 (PDF 7); proof pp. ec3–ec4 (PDF 40–41)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Model
import Definitions.Def_CarlssonPartition_Approx_Supplement_AdmissiblePolicies

noncomputable section

open Filter Topology MeasureTheory
open scoped ENNReal

namespace CarlssonPartition.Approx.Supplement

/-- Theorem 4 (p. 10), corrected to Poisson arrivals: for EVERY partition of `R` (null and
empty districts allowed), the region partitioning policy is optimal in light traffic. Two
clauses: every admissible policy (flexible or dedicated, at every positive rate) has expected
delivery time at least the light-traffic value `∬_R ‖x - x0‖ f / v + s̄` of (EC.1) with the
speed divisor of p. ec4; and some admissible dedicated policies attain that value in the
limit `λ → 0⁺`. Poisson arrivals are the arrival law of the source proof (the M/G/1 queues
of p. ec4); `theorem_4_clustered_renewal_counterexample` shows the printed claim fails for
general rate-dependent renewal families. -/
theorem theorem_4 (M : Model) (hStanding : M.Standing) (hHom : M.Homogeneous)
    (Rs : Fin M.spatial.m → Set CarlssonPartition.Equitable.Plane)
    (hP : M.spatial.IsPartition Rs)
    (Ω : Type) [MeasurableSpace Ω] (A : M.InputFamily Ω) (hA : A.Poisson) :
    (∀ (lam : {lam : ℝ // 0 < lam}) (U : Type) [MeasurableSpace U]
        (π : PolicyRealization (A.input lam).renewal U M.spatial.m),
        π.Admissible M.spatial.x0 M.spatial.v M.spatial.q → M.lightValue ≤ π.cost) ∧
    ∃ (U : Type) (_ : MeasurableSpace U)
      (π : ∀ lam : {lam : ℝ // 0 < lam},
        PolicyRealization (A.input lam).renewal U M.spatial.m),
      (∀ lam, (π lam).Admissible M.spatial.x0 M.spatial.v M.spatial.q ∧
        (π lam).DedicatedTo Rs) ∧
      Tendsto (fun lam => (π lam).cost)
        (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 M.lightValue) := by sorry

end CarlssonPartition.Approx.Supplement
