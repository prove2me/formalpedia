-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_9
-- name    : CarlssonPartition.Approx.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:35:15.364802+00:00
-- url     : https://prove2.me/theorems/8a5c07cf-80f4-476c-8ca4-8f28862a27c7
-- title:
--   Theorem 9, p. 14 (corrected: q ≥ 2 and finite mean load) — heterogeneous-service equitable partition is asymptotically optimal
-- statement:
--   Let $R\subset\mathbb R^2$ be the compact convex service region with depot $x_0\in R$ and Lipschitz demand density $f\ge0$, $\iint_R f=1$; let $m\ge1$ vehicles of speed $v>0$ and capacity $q\ge2$ serve orders whose on-site service time at location $x$ has a law $S(x)$ on $[0,\infty)$ with finite mean $\bar s(x)$ and variance; assume $\iint_R\bar s(x)f(x)\,dx<\infty$, and let $\beta>0$ be the constant of Theorem 8. For a region $D$, a density $g$ on $D$, $k$ vehicles and arrival rate $a$, write
--   $$
--   W_k(a;D,g)=\frac{a}{k}\iint_D\bar s\,g+\frac{2a\iint_D\|x-x_0\|g}{kvq},\qquad
--   \tilde L_k(a;D,g)=\frac{\beta^2 a(1-1/q)^2\big[\iint_D\sqrt g\big]^2}{2k^2v^2\big(1-W_k(a;D,g)\big)^2}
--   $$
--   for the heterogeneous workload factor ($\rho=\lambda\iint_R\bar s f/m$) and the leading term of Theorem 8. Let $\{R_1,\dots,R_m\}$ be a partition of $R$ satisfying, for every $i$,
--   $$
--   \iint_{R_i}\sqrt f=\frac1m\iint_R\sqrt f,\qquad\iint_{R_i}\big(\bar s(x)vq+2\|x-x_0\|\big)f=\frac1m\iint_R\big(\bar s(x)vq+2\|x-x_0\|\big)f .
--   $$
--   Write $p_i=\iint_{R_i}f$ and $f_i=f/p_i$. Suppose the benchmark $\tilde\pi^*$ of Theorem 8 satisfies $T(\tilde\pi^*)(\lambda)/\tilde L_m(\lambda;R,f)\to1$ as $W_m(\lambda;R,f)\to1^-$, and that each district's optimal single-vehicle policy satisfies $T_i(a)/\tilde L_1(a;R_i,f_i)\to1$ as $W_1(a;R_i,f_i)\to1^-$. Then
--   $$
--   \frac{\sum_{i=1}^m p_i\,T_i(\lambda p_i)}{T(\tilde\pi^*)(\lambda)}\longrightarrow1\qquad\text{as }W_m(\lambda;R,f)\to1^- .
--   $$
--   This extends the two equitable conditions of Theorem 6 to location-dependent service: the load condition weights each location by its own mean service time.
--
--   **Formalization Note** The routing model enters only through the asymptotics of Theorem 8, as in the proof (p. ec12): the delivery times are real functions of the rate. Service is a Markov kernel of laws on $\mathbb R$; the mean $\bar s(x)$ is its expectation. Two hypotheses are added: integrability of $\bar s f$ on $R$ (otherwise the workload is infinite for every rate and no heavy-traffic regime exists) and $q\ge2$ (at $q=1$ the leading term is zero). DISPROOF.md records that Theorem 8's asymptotics can fail for actual policies when the spatial second moment of service is infinite; the hypothesis on $T(\tilde\pi^*)$ is then not satisfied by any actual policy.
--
--   Differences from the source:
--   - encoding: "The resulting region partitioning policy is asymptotically optimal if every vehicle follows the optimal single-vehicle policy within the subregion" (p. 14), with heterogeneous service and benchmark π̃* of Theorem 8. → Tstar (the benchmark π̃* of Theorem 8) and the district delivery times T i are real functions of the arrival rate constrained by Theorem 8's leading term with heterogeneous workload ρ + 2λ∬‖x − x_0‖f/(mvq), ρ = λ∬ s̄(x)f/m: Tstar with m vehicles in global heavy traffic, T i a with one vehicle, district rate a and density f_i along the district heavy filter. The conclusion evaluates T i at λ_i = λ ∬_{R_i} f in Σ p_i T_i.; reason: The proof (p. ec12, PDF 49) is "similar to that of Theorem 6" and changes only the denominator of T_i to the heterogeneous workload with ρ_i = λ_i∬ s̄ f_i; it uses the delivery times only through these asymptotics.
--   - correction: Mean and variance of S(x) finite at every x (p. 13, PDF 14); ρ = λ∬_R s̄(x)f(x)dx/m. → Added hypothesis hmean: s̄(x)f(x) is integrable on R.; reason: The workload factor is a real number in (0,1) on the source's heavy-traffic domain (p. 7, PDF 8) and ρ is displayed as a real integral (PDF 14). Pointwise finiteness does not make ∬ s̄ f finite; when it is infinite the workload is +∞ for every λ > 0, no heavy-traffic regime exists, and in Lean the Bochner integral would silently return 0. Excluded cases: service fields with ∬_R s̄ f = ∞.
--   - correction: Capacity q ∈ ℕ₊ (p. 6), including q = 1. → Added hypothesis 2 ≤ q; q = 1 is excluded.; reason: At q = 1 the leading term of Theorem 8 has the factor (1 − 1/q)^2 = 0, so it does not characterize the benchmark, the proof divides by it, and the ratio premises would be unsatisfiable. Theorem 8 itself fails at q = 1 (milestone theorem_8_capacity_one_counterexample). Excluded case: unit capacity.
--   - encoding: {R_1,…,R_m} is a partition of R; heavy traffic is "ρ + 2λ∬_R‖x − x_0‖f/mvq → 1". → Partition up to Lebesgue-null sets (null-measurable, pairwise a.e. disjoint, union R); heavy traffic is the comap of the workload factor into the left neighbourhood of 1.; reason: Same conventions as the published base Setting; boundaries of districts carry no demand.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 14 (PDF 15), Theorem 9; with Theorem 8, p. 14, and the heterogeneous model, p. 13 (PDF 14); proof p. ec12 (PDF 49)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Heterogeneous

open Filter Topology MeasureTheory

namespace CarlssonPartition.Approx.Supplement

open CarlssonPartition.Equitable (Plane)

/-- Theorem 9 (p. 14): with heterogeneous, location-dependent service of mean `s̄(x)`, a
partition equitable in `∬ √f` and in `∬ (s̄(x) v q + 2 ‖x - x0‖) f` gives an asymptotically
optimal region partitioning policy when every vehicle follows the optimal single-vehicle
policy in its subregion. As the proof (p. ec12, "similar to that of Theorem 6") uses it, the
benchmark `Tstar` is the policy of Theorem 8, characterized by Theorem 8's leading term with
the heterogeneous workload `ρ + 2λ∬‖x - x0‖f/(mvq)`, `ρ = λ∬ s̄(x) f / m`; each district's
delivery time `T i a`, at its own rate `a`, obeys the same leading term with one vehicle and
the conditional density `f_i`. The fleet sum evaluates it at `λ_i = λ ∬_{R_i} f`.
`hmean` (finite spatial mean of `s̄`) is the source's requirement that the workload factor
take values in `(0,1)`; `2 ≤ q` excludes the capacity at which the leading term vanishes. -/
theorem theorem_9 (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks Plane) (hS : serviceStanding I S) (hq : 2 ≤ I.q)
    (hmean : finiteMeanDomain I S I.R I.f)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs)
    (h1 : ∀ i, (∫ x in Rs i, Real.sqrt (I.f x)) =
      (1 / (I.m : ℝ)) * ∫ x in I.R, Real.sqrt (I.f x))
    (h2 : ∀ i, (∫ x in Rs i, (S.mean x * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x) =
      (1 / (I.m : ℝ)) * ∫ x in I.R, (S.mean x * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (Tstar : ℝ → ℝ)
    (hstar : Tendsto (fun lam => Tstar lam / finiteLeading I S I.m lam I.R I.f)
      (finiteHeavy I S I.m I.R I.f) (𝓝 1))
    (T : Fin I.m → ℝ → ℝ)
    (hT : ∀ i, Tendsto
      (fun a => T i a / finiteLeading I S 1 a (Rs i) (I.fSub (Rs i)))
      (finiteHeavy I S 1 (Rs i) (I.fSub (Rs i))) (𝓝 1)) :
    Tendsto (fun lam => (∑ i, I.pr (Rs i) * T i (I.lamSub lam (Rs i))) / Tstar lam)
      (finiteHeavy I S I.m I.R I.f) (𝓝 1) := by sorry

end CarlssonPartition.Approx.Supplement
