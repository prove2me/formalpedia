-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_5
-- name    : CarlssonPartition.Approx.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:29:56.41944+00:00
-- url     : https://prove2.me/theorems/09c46ae3-8e8a-44fe-9188-1562a6f8f147
-- title:
--   Theorem 5, p. 10 (corrected: q ≥ 2) — three equitable conditions give asymptotic optimality of the region partitioning policy
-- statement:
--   Let $R\subset\mathbb R^2$ be the compact convex service region with depot $x_0\in R$ and Lipschitz demand density $f\ge0$, $\iint_R f=1$; let $m\ge1$ vehicles of speed $v>0$ and capacity $q\ge2$ serve orders with mean on-site time $\bar s\ge0$, and let $\beta>0$ be the constant of Theorem 3. For a region $D$, a density $g$ on $D$, $k$ vehicles and arrival rate $a$, write
--   $$
--   L_k(a;D,g)=\frac{\beta^2 a(1-1/q)^2\big[\iint_D\sqrt{g}\big]^2}{2k^2v^2\big(1-a\bar s/k-2a\iint_D\|x-x_0\|g/(kvq)\big)^2}
--   $$
--   for the leading term of Theorem 3. Let $\{R_1,\dots,R_m\}$ be a partition of $R$ satisfying, for every $i$,
--   $$
--   \iint_{R_i} f=\frac1m,\qquad\iint_{R_i}\sqrt f=\frac1m\iint_R\sqrt f,\qquad\iint_{R_i}\|x-x_0\|f=\frac1m\iint_R\|x-x_0\|f .
--   $$
--   Write $p_i=\iint_{R_i}f$, $\lambda_i=\lambda p_i$ and $f_i=f/p_i$. Suppose the benchmark delivery time satisfies Theorem 3, $T(\pi^*)(\lambda)/L_m(\lambda;R,f)\to1$ as the workload factor tends to $1$ from below, and that each district's optimal single-vehicle policy satisfies Theorem 3 with one vehicle, $T_i(a)/L_1(a;R_i,f_i)\to1$ as the district's own workload factor tends to $1$. Then the region partitioning policy is asymptotically optimal:
--   $$
--   \frac{\sum_{i=1}^m p_i\,T_i(\lambda p_i)}{T(\pi^*)(\lambda)}\longrightarrow1\qquad\text{in heavy traffic.}
--   $$
--   This is the three-condition companion of Theorem 6: equal demand mass, equal $\iint\sqrt f$ and equal radial load make every district's heavy-traffic delivery time match the fleet benchmark.
--
--   **Formalization Note** The stochastic routing model enters only through Theorem 3 (Bertsimas–van Ryzin), as in the paper's proof (pp. ec4–ec5): $T(\pi^*)$ and the $T_i$ are real functions of the rate constrained by its asymptotics, as in the published Theorem 6. Ratios tending to $1$ encode "$\sim$"; heavy traffic is the filter along which the workload factor tends to $1$ from below; partitions are read up to null sets. The added hypothesis $q\ge2$ excludes unit capacity, where Theorem 3's leading term is zero.
--
--   Differences from the source:
--   - encoding: "The resulting region partitioning policy is asymptotically optimal if every vehicle follows the optimal single-vehicle policy within the subregion", i.e. T(π)/T(π*) → 1 in heavy traffic (p. 10). → Tstar (the benchmark π* of Theorem 3) and the district delivery times T i are real functions of the arrival rate constrained by Theorem 3: Tstar over the m-vehicle leading term tends to 1 in global heavy traffic, and T i a over the one-vehicle leading term of district i (rate a, density f_i) tends to 1 along the district heavy filter. The conclusion evaluates T i at λ_i = λ ∬_{R_i} f inside the total expectation Σ p_i T_i.; reason: The paper characterizes π* and the optimal single-vehicle district policy only through Theorem 3 (Bertsimas–van Ryzin, p. 8; PDF 9 states its omitted technical assumptions are not listed). The proof on pp. ec4–ec5 (PDF 41–42) uses exactly these two asymptotics and the total expectation. The same encoding is used by the published Theorem 6 of this paper.
--   - correction: Capacity q ∈ ℕ₊ (p. 6), including q = 1. → Added hypothesis 2 ≤ q; q = 1 is excluded.; reason: At q = 1 the leading term of Theorem 3 (p. 8) contains the factor (1 − 1/q)^2 = 0, so Theorem 3 gives no characterization of T(π*) or of the district policies, and the proof on pp. ec4–ec5 divides by this zero term. Without the hypothesis the ratio premises would be unsatisfiable at q = 1 and the statement vacuous there. Excluded case: unit capacity.
--   - encoding: {R_1,…,R_m} is a partition of R; heavy traffic is "ρ + 2λ∬_R‖x − x_0‖f/mvq → 1". → Partition up to Lebesgue-null sets (null-measurable, pairwise a.e. disjoint, union R); heavy traffic is the comap of the workload factor into the left neighbourhood of 1.; reason: Same conventions as the published base Setting; boundaries of districts carry no demand.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 10 (PDF 11), Theorem 5; with Theorem 3, p. 8 (PDF 9); proof pp. ec4–ec5 (PDF 41–42)

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

open Filter Topology MeasureTheory

namespace CarlssonPartition.Approx.Supplement

open CarlssonPartition.Equitable

/-- Theorem 5 (p. 10): a partition equitable in demand mass, in `∬ √f` and in the radial
load `∬ ‖x - x0‖ f` gives an asymptotically optimal region partitioning policy when every
vehicle follows the optimal single-vehicle policy in its subregion. As in the published
Theorem 6, Theorem 3 of Bertsimas and van Ryzin enters through the delivery-time functions:
`Tstar` is the benchmark of Theorem 3 for the whole fleet, and `T i a` is the delivery time
of district `i` at its OWN arrival rate `a` (Theorem 3 with one vehicle). The fleet sum
evaluates it at `a = lamSub lam (Rs i)`. Its connection
to the stochastic model is the one the paper itself makes: the source characterizes the
benchmark `T(π*)` and each district's optimal single-vehicle policy only through Theorem 3.
Capacity `q = 1` is excluded explicitly (`2 ≤ q`): there Theorem 3's leading term is zero,
so its ratio hypotheses cannot hold and the source's proof (pp. ec4–ec5) divides by zero. -/
theorem theorem_5 (I : CarlssonPartition.Equitable.Instance) (hI : I.Standing) (hq : 2 ≤ I.q)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs)
    (h0 : ∀ i, (∫ x in Rs i, I.f x) = 1 / (I.m : ℝ))
    (h1 : ∀ i, (∫ x in Rs i, Real.sqrt (I.f x)) =
      (1 / (I.m : ℝ)) * ∫ x in I.R, Real.sqrt (I.f x))
    (h2 : ∀ i, (∫ x in Rs i, ‖x - I.x0‖ * I.f x) =
      (1 / (I.m : ℝ)) * ∫ x in I.R, ‖x - I.x0‖ * I.f x)
    (Tstar : ℝ → ℝ)
    (hstar : Tendsto (fun lam => Tstar lam / I.bvrLeading I.m lam I.R I.f)
      (I.heavy I.m I.R I.f) (𝓝 1))
    (T : Fin I.m → ℝ → ℝ)
    (hT : ∀ i, Tendsto
      (fun a => T i a / I.bvrLeading 1 a (Rs i) (I.fSub (Rs i)))
      (I.heavy 1 (Rs i) (I.fSub (Rs i))) (𝓝 1)) :
    Tendsto (fun lam => (∑ i, I.pr (Rs i) * T i (I.lamSub lam (Rs i))) / Tstar lam)
      (I.heavy I.m I.R I.f) (𝓝 1) := by sorry

end CarlssonPartition.Approx.Supplement
